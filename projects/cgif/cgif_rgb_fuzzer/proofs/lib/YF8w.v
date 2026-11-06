(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition lit8 (a v : Z) : YQ0b.region := YQ0b.mkRegion None a (a + 8) 0 0 [YQ0b.mkChunk a (CVal 8 (SLit v))].
Definition lit4 (a v : Z) : YQ0b.region := YQ0b.mkRegion None a (a + 4) 0 0 [YQ0b.mkChunk a (CVal 4 (SLit v))].
Definition lit1 (a v : Z) : YQ0b.region := YQ0b.mkRegion None a (a + 1) 0 0 [YQ0b.mkChunk a (CVal 1 (SLit v))].
Definition atom8 (a : Z) (n : nat) : YQ0b.region := YQ0b.mkRegion None a (a + 8) 0 0 [YQ0b.mkChunk a (CVal 8 (SOff n 0))].
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
Definition UREGS0 {imgk : img} : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFX_TP)) 13%bv (SLit 0)) 14%bv (SLit 1)) 15%bv (SLit 30).
Definition R_S : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- UNW_STK) 0 (- UNW_STK) 0 [].
Definition R_C : YQ0b.region := YQ0b.mkRegion (Some aC) 152 160 0 0 [YQ0b.mkChunk 152 (CVal 8 (SOff aT 0))].
Definition R_T1 : YQ0b.region := YQ0b.mkRegion (Some aT) 8 41 0 0
[YQ0b.mkChunk 8 (CVal 8 (SOff aTOP 0)); YQ0b.mkChunk 16 (CVal 8 (SOff aTOP (- kStackSpan))); YQ0b.mkChunk 40 (CVal 1 (SLit 0))].
Definition R_T2 : YQ0b.region := YQ0b.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1)
[YQ0b.mkChunk t_unwinding (CVal 1 (SLit 0))].
Definition R_O1a0 : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 8 12 8 12 [].
Definition R_O1b0 : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 16 24 16 24 [].
Definition R_O2 : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 2056 2064 2056 2064 [].
Definition R_F (b : nat) : YQ0b.region := YQ0b.mkRegion (Some b) (- 16) 0 0 0
[YQ0b.mkChunk (- 16) (CVal 8 (SOff aNFP 0)); YQ0b.mkChunk (- 8) (CVal 8 (SOff aRA 0))].
Definition UCONST {imgk : img} : smem :=
[ lit1 (0xaae98 + D_10c0) 1; lit1 (0xa9a20 + D_10c0) 1; lit4 (0xa9a24 + D_10c0) 0; lit8 (TFX_TP - 88) TFX_TSD; atom8 TFX_TSD aC;
lit8 (0xa2140 + D_10f0) (0x139c60 + D_10c0); lit8 (0x139c60 + D_10c0) 4096 ].
Definition UMEM0 {imgk : img} : smem := [R_S; R_O1a0; R_O1b0; R_O2; R_F 12%nat] ++ UCONST ++ [R_C; R_T1; R_T2].
Definition SS_U0 {imgk : img} : sstate := mkSS A_UnwindImpl UREGS0 UMEM0 None UF0.
Definition run_rt {imgk : img} (ss : sstate) : sstate := fst (sym_runN tfxsegs tfxtbl_rtA FUEL ss).
Definition runto_rt {imgk : img} (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfxsegs tfxtbl_rtA FUEL pc ss).
Definition S1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (run_rt SS_U0))).
Definition c_f0_bad : acond := mkAC Instr.BC_GEU (SOff 12%nat 0) (SOff aTOP (-16)).
Definition c_f0_ok : acond := mkAC Instr.BC_LTU (SOff 12%nat 0) (SOff aTOP (-16)).
Definition R_S' {imgk : img} : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- UNW_STK) 0 (- UNW_STK) 0
[YQ0b.mkChunk (-144) (CVal 8 (SOff aTOP 0)); YQ0b.mkChunk (-136) (CVal 8 (SLit 1)); YQ0b.mkChunk (-128) (CVal 8 (SLit 0));
YQ0b.mkChunk (-120) (CVal 8 (SOff 10%nat 0)); YQ0b.mkChunk (-112) (CVal 8 (SOff 11%nat 0)); YQ0b.mkChunk (-104) (CVal 8 (SLit 30));
YQ0b.mkChunk (-96) (CVal 8 (SOff 12%nat 0)); YQ0b.mkChunk (-88) (CVal 8 (SLit (0x5afbc + D_2c4))); YQ0b.mkChunk (-80) (CVal 8 (SOff 24%nat 0));
YQ0b.mkChunk (-72) (CVal 8 (SOff 23%nat 0)); YQ0b.mkChunk (-64) (CVal 8 (SOff 22%nat 0)); YQ0b.mkChunk (-56) (CVal 8 (SOff 21%nat 0));
YQ0b.mkChunk (-48) (CVal 8 (SOff 20%nat 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19%nat 0)); YQ0b.mkChunk (-32) (CVal 8 (SOff 18%nat 0));
YQ0b.mkChunk (-24) (CVal 8 (SOff 9%nat 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8%nat 0)); YQ0b.mkChunk (-8) (CVal 8 (SOff 1%nat 0))].
Definition R_O1a (z : sv) : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 8 12 8 12 [YQ0b.mkChunk 8 (CVal 4 z)].
Definition R_O1b : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 16 24 16 24 [YQ0b.mkChunk 16 (CVal 8 (SOff 11%nat 0))].
Definition R_O2' : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 2056 2064 2056 2064 [YQ0b.mkChunk 2056 (CVal 8 (SOff 12%nat 0))].
Definition R_T2' : YQ0b.region := YQ0b.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1)
[YQ0b.mkChunk t_unwinding (CVal 1 (SLit 1))].
Definition LFIX {imgk : img} : smem := [R_S'; R_O1b; R_O2'] ++ UCONST ++ [R_C; R_T1; R_T2'].
Definition S_LH0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto_rt (0x73a18 + D_2c4) (YQ09.add_cond S1 c_f0_ok)))).

Definition R_Q : YQ0b.region := YQ0b.mkRegion (Some aQ) 0 8 0 8 [].
Definition LREGS {imgk : img} : list sv :=
[SLit 0; SLit (0x5afbc + D_2c4); SOff 2 (-144); SOff 3 0; SLit TFX_TP; SOff 10 2047; SOff 12 0; SOff 7 0; SLit 30; SOff aTOP (-16); SOff 10 0; SOff 11 0; SOff aB 0; SLit 4096;
SOff 10 16; SOff aZ 0; SOff aHAV 0; SOff (S aHAV) 0; SLit (0x139c60 + D_10c0); SOff 10 0; SLit 0; SLit 1; SOff aTOP 0; SOff aT 0; SOff aT 2047; SOff 25 0; SOff 26 0;
SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]%nat.
Definition LATOMS : list (nat * afact) :=
UF_atoms ++ [(aB, mkAF kHighMemBeg kHighMemEnd 3); (aZ, mkAF 1 30 0); (aQ, mkAF kHighMemBeg kHighMemEnd 3);
(aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0)].
Definition LCONDS : list acond := [c_f0_ok] ++ UF_conds.
Definition LALIAS : sv * sv := (SAlu Instr.ALU_ADD (SOff 10%nat 16) (SAlu Instr.ALU_SLL (SOff aZ 0) (SLit 3)), SOff aQ 0).
Definition LF0 : facts := mkFacts LATOMS LCONDS [].
Definition LF : facts := mkFacts LATOMS LCONDS [LALIAS].
Definition LMEM {imgk : img} : smem := R_F aB :: R_O1a (SOff aZ 0) :: LFIX.
Definition A_LOOP {imgk : img} : Z := (0x73a18 + D_2c4).
Definition S_L {imgk : img} : sstate := mkSS A_LOOP LREGS LMEM None LF.
Definition R_Fb (b : nat) : YQ0b.region := YQ0b.mkRegion (Some b) (- 8) 0 0 0 [YQ0b.mkChunk (- 8) (CVal 8 (SOff aRA 0))].
Definition LATOMSB : list (nat * afact) :=
UF_fixed ++ [(aRA, mkAF 0 4095 0); (aB, mkAF kHighMemBeg kHighMemEnd 3); (aZ, mkAF 1 30 0); (aQ, mkAF kHighMemBeg kHighMemEnd 3);
(aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0)].
Definition LFB : facts := mkFacts LATOMSB LCONDS [].
Definition LMEMB {imgk : img} : smem := R_Fb aB :: R_O1a (SOff aZ 0) :: LFIX.
Definition S_LB {imgk : img} : sstate := mkSS A_LOOP LREGS LMEMB None LFB.
Definition XREGS {imgk : img} : list sv :=
[SLit 0; SLit (0x5afbc + D_2c4); SOff 2 (-144); SOff 3 0; SLit TFX_TP; SOff 10 2047; SOff 12 0; SOff 7 0; SLit 30; SOff aTOP (-16); SOff 10 0; SOff 11 0; SOff aHAV 0; SLit 4096;
SOff 44 0; SOff (S aHAV) 0; SOff (S (S aHAV)) 0; SOff (S (S (S aHAV))) 0; SLit (0x139c60 + D_10c0); SOff 10 0; SLit 0; SLit 1; SOff aTOP 0; SOff aT 0; SOff aT 2047;
SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]%nat.
Definition XATOMS : list (nat * afact) :=
UF_fixed ++ [(aZ, mkAF 1 30 0); (aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S (S aHAV), mkAF 0 (2 ^ 64 - 1) 0);
(S (S (S aHAV)), mkAF 0 (2 ^ 64 - 1) 0); (44%nat, mkAF 0 (2 ^ 64 - 1) 0)].
Definition XF : facts := mkFacts XATOMS UF_conds [].
Definition XMEM {imgk : img} : smem := R_O1a (SOff aZ 0) :: LFIX.
Definition A_EXIT {imgk : img} : Z := (0x73a54 + D_2c4).
Definition S_X {imgk : img} : sstate := mkSS A_EXIT XREGS XMEM None XF.

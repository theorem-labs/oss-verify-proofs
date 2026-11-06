(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twins of the four loop states of libreac/fuzz_knock's ASan harness
   walk of LLVMFuzzerTestOneInput (fuzz_knock.asan-ubsan, sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82; 350 words at 0x7eed0, size 0x578), made from
   lib/A/APgLoop0.v sections 3-5 (ss_L / ss_T / ss_M / ss_C and the memory
   shape they share), the way proofs/cgif/cgif_file_fuzzer/lib/YCf7.v is made from A/ACf7.v at c8557374ad2e: the walk
   framework imports move to the lib/AU twins, every pc is the asan-ubsan one, and the registers and spills follow the
   asan-ubsan code. rule 24: no function proved. Definitions and structural lemmas only. *)

(* The instruction-by-instruction comparison of the two images and the segment cut these states come from is
   (internal path). ss_H (0x7f004) and ss_X (0x7f2c4) are a Theorem Labs lane's,
   in lib/AU/APgMain0.v and lib/AU/APgMain7.v: this file Requires APgMain7 for ss_X and rt_X_saves and defines neither,
   and Requires lib/AU/APgRt.v for rt_X_at_rt (APgMain7's S7 lemma named at the AU context record).
   ss_P (0x7f0d4, the S1 -> S2 join) is a Theorem Labs lane's and is not stated here.

   THE CUT (asan pc -> asan-ubsan pc)
     ss_L 0x7f10c -> 0x7f154   the loop head, after the rem test. In the asan-ubsan image the rem test `beqz s9` is at
                               the head of the loop (0x7f150, target ss_X 0x7f2c4); the asan image tests rem before the
                               loop (0x7f0dc) and at its back edge (0x7f248). ss_L is put after 0x7f150, so S2 and S6
                               each end with that test, as in the asan cut, and ss_L keeps 1 <= rem.
     ss_T 0x7f194 -> 0x7f1ec   after the one to three input reads (`or a1,a2,a1`).
     ss_M 0x7f1c4 -> 0x7f21c   after `now += dt << sh` and the optional reac_knock_heard call (0x7f520, RA 0x7f214).
     ss_C 0x7f21c -> 0x7f270   after the optional reac_knock_step call (0x7f5b0, RA 0x7f230) and its four aborts.

   WHAT DIFFERS FROM THE ASAN STATES, AND WHY (asan-ubsan code; the asan code in brackets)
   - x24 (s8) = d, the DRIVEN flag: `li s8,0` 0x7f128, `li s8,1` 0x7f254, `bgtz s8` 0x7f238, `bnez s8` 0x7f25c,
     `bne a0,s8` 0x7f274, `beqz s8` 0x7f278  [s8 = 4094, the loop bound: lui s8,0x1 / addiw s8,s8,-2 0x7f0ec / 0x7f0f4].
   - x27 (s11) = 1, the constant of the UBSan guards `bgeu s11,..` 0x7f158 / 0x7f188 / 0x7f1c4 and of `bne s9,s11`
     0x7f174 / `bne a0,s11` 0x7f234: `li s11,1` 0x7f134  [s11 = d].
   - x26 (s10) = the trip countdown, 4096 - i: `lui s10,0x1` 0x7f130, `addiw s10,s10,-1` 0x7f294, `bnez s10,0x7f150`
     0x7f298  [s10 = i counting up from 0: li s10,0 0x7f0e0, `bltu s8,s10` 0x7f240, `addiw s10,s10,1` 0x7f244]. Its slot
     is N_cnt (the asan N_i, slot 302), with range [1, 4096] (i in [0, 4095] both ways).
   - spills 32(s1) = 499999999 and 40(s1) = 500000000: `addiw a1,a0,1279; sd a1,32(s1)` 0x7f13c / 0x7f140 and
     `addiw a0,a0,1280; sd a0,40(s1)` 0x7f144 / 0x7f148  [32(s1) = 500000000, 40(s1) = 499999999]. The two step checks
     read them with the swapped compare: `bltu a0,a1` 0x7f250 (a1 = 40(s1)) and `bltu a1,a0` 0x7f26c (a1 = 32(s1)).
   - the four constant cells of the lib record are the asan-ubsan image's: 615960 = 0x96618, 648568 = 0x9e578,
     616048 = 0x96670, 648576 = 0x9e580 (lib/AU/YCeh.v:21-24)  [615888, 648504, 615976, 648512].
   Everything else is the asan state's: s1 = sp = sp1 (slot 70), s0 = sp0 (slot 2), s4 = F + 32, s6 = SB + F/8
   (slot 88), s9 = rem, s3 = cur, s2 = h, s5 = now, s7 = ev; spills 16 / 24 / 80(s1) = F, 48(s1) = quiet, 56(s1) = SB;
   the frame's 16 shadow bytes f1 x4, 0 x5, f3 x7; k at F + 32; the 13 saves; the atoms and the alias of ss_H.

   The env slots are lib/A/APgLoop0.v's (300-343 and the havoc windows 700 / 720 / 740 / 760). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt APgMain7.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================== the env slots of the loop [lib/A/APgLoop0.v:331-345] ===================== *)
Definition N_rem := 300%nat.   Definition N_cur := 301%nat.   Definition N_cnt := 302%nat.
Definition N_d := 303%nat.     Definition N_h := 304%nat.     Definition N_now := 305%nat.
Definition N_quiet := 306%nat. Definition N_op := 307%nat.
Definition N_due := 308%nat.   Definition N_hns := 309%nat.   Definition N_st := 310%nat.
Definition N_g := 311%nat.     Definition N_p1 := 312%nat.    Definition N_p2 := 313%nat.
Definition N_ev := 320%nat.    Definition N_lo := 321%nat.    Definition N_hi := 322%nat.
Definition N_remT := 323%nat.  Definition N_curT := 324%nat.
Definition N_nowM := 331%nat.  Definition N_hM := 332%nat.    Definition N_quietM := 333%nat.
Definition N_stM := 334%nat.   Definition N_hnsM := 335%nat.
Definition N_dC := 340%nat.    Definition N_stC := 341%nat.   Definition N_dueC := 342%nat.
Definition N_gC := 343%nat.
Definition RT_LN : nat := 760%nat.
Definition RT_TN : nat := 700%nat.
Definition RT_MN : nat := 720%nat.
Definition RT_CN : nat := 740%nat.

(* the registers the loop does not keep live [lib/A/APgLoop0.v:347-362]: the same in both images (s8 / s10 / s11 are
   live in both; s7 carries ev from 0x7f170 to 0x7f220, so it is dead only at ss_L and ss_C; ss_T keeps a1 / a2 for
   `or a1,a2,a1` at 0x7f1ec) *)
Definition rt_loop_deads : list nat :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition rt_loop_deads_bv : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition rt_loop_deadsT : list nat :=
[1; 5; 6; 7; 10; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition rt_loop_deadsT_bv : list (bv 5) :=
[1; 5; 6; 7; 10; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition rt_loop_deads7 : list nat :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat.
Definition rt_loop_deads7_bv : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%bv.

(* ===================== the memory shape every loop state carries [lib/A/APgLoop0.v:364-426] ===================== *)
(* the 16 shadow bytes of the 128-byte frame: f1 x 4, 0 x 5 (k, unpoisoned by S2 at 0x7f0e4-0x7f0f0 and 0x7f100),
   f3 x 7 *)
Definition rl_shadow : YP09.region :=
YP09.mkRegion (Some 88%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601));
YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601));
YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0));
YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 8 (CVal 1 (SLit 0));
YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551603));
YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551603));
YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551603));
YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551603))].
(* the frame header F[0,32), written by S0 *)
Definition rl_header : YP09.region :=
YP09.mkRegion (Some 75%nat) 0 32 0 32 [].
(* the flag slot F[112,128): the word at F+120 is the fake-frame flag address (S7 stores through it) *)
Definition rl_flag : YP09.region :=
YP09.mkRegion (Some 75%nat) 112 128 112 128 [YP09.mkChunk 120 (CVal 8 (SOff 87 0))].
(* k = F+32 .. F+72 (`addi s4,a7,32` at 0x7f0d8, a7 = F), over the seven field slots *)
Definition rl_k (nst np1 nop ndue nhns ng np2 : nat) : YP09.region :=
YP09.mkRegion (Some 75%nat) 32 72 32 72
[YP09.mkChunk 32 (CVal 4 (SOff nst 0)); YP09.mkChunk 36 (CVal 4 (SOff np1 0));
YP09.mkChunk 40 (CVal 8 (SOff nop 0)); YP09.mkChunk 48 (CVal 8 (SOff ndue 0));
YP09.mkChunk 56 (CVal 8 (SOff nhns 0)); YP09.mkChunk 64 (CVal 4 (SOff ng 0));
YP09.mkChunk 68 (CVal 4 (SOff np2 0))].
(* the spills off s1: 16 = F (0x7f0d4 sd a7,16(s1)), 24 = F (0x7f000 sd a6,24(s1)), 32 = 499999999 (0x7f140),
   40 = 500000000 (0x7f148), 48 = quiet (0x7f14c, 0x7f218), 56 = SB (0x7ef34), 80 = F (0x7ef78 sd a7,80(s1)) *)
Definition rl_spill (nq : nat) : YP09.region :=
YP09.mkRegion (Some 70%nat) 16 88 16 88
[YP09.mkChunk 16 (CVal 8 (SOff 75 0)); YP09.mkChunk 24 (CVal 8 (SOff 75 0));
YP09.mkChunk 32 (CVal 8 (SLit 499999999)); YP09.mkChunk 40 (CVal 8 (SLit 500000000));
YP09.mkChunk 48 (CVal 8 (SOff nq 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0));
YP09.mkChunk 80 (CVal 8 (SOff 75 0))].
(* the thirteen callee-saved words the prologue wrote at sp0-104 .. sp0-8 (lib/AU/APgMain7.v rt_X_saves) *)
Definition rl_saves : YP09.region :=
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 rt_X_saves.
(* the four constant cells of the lib record, at the asan-ubsan addresses [lib/AU/YCeh.v:21-24] *)
Definition rl_consts : smem :=
[YP09.mkRegion None 615960 615968 0 0 [YP09.mkChunk 615960 (CVal 8 (SLit 648568))];
YP09.mkRegion None 648568 648576 0 0 [YP09.mkChunk 648568 (CVal 8 (SOff 32 0))];
YP09.mkRegion None 616048 616056 0 0 [YP09.mkChunk 616048 (CVal 8 (SLit 648576))];
YP09.mkRegion None 648576 648580 0 0 [YP09.mkChunk 648576 (CVal 4 (SLit 1))]].
Definition rl_mem (nst np1 nop ndue nhns ng np2 nq : nat) : smem :=
rl_k nst np1 nop ndue nhns ng np2 :: rl_header :: rl_shadow :: rl_flag :: rl_spill nq :: rl_saves :: rl_consts.
(* the alias that makes a write through s6 a write to the frame's shadow *)
Definition rl_alias : list (sv * sv) :=
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)].
(* the context record's atoms, as S0 leaves them (ss_H's facts, the same in both images) *)
Definition rl_atoms0 : list (nat * afact) :=
[(88%nat, mkAF 2147451392 17594333495296 2); (87%nat, mkAF 4096 140737479966720 0);
(75%nat, mkAF 4096 140737479966720 5); (70%nat, mkAF 70368744177152 140737488355328 5);
(2%nat, mkAF 70368744177664 140737488355328 4); (11%nat, mkAF 0 67108863 0);
(32%nat, mkAF 2147450880 2147450880 0)].
Definition rl_atomsK (nst nop ndue nhns ng np1 np2 : nat) : list (nat * afact) :=
[(nst, mkAF 0 2 0); (ng, mkAF 0 1 0); (np1, mkAF 0 4294967295 0); (np2, mkAF 0 4294967295 0);
(nop, mkAF 0 9223372036854775807 0); (ndue, mkAF 0 18446744073709551615 0);
(nhns, mkAF 0 9223406396593514176 0)].
(* the cursor's address window [4096, 2^47 - 2^23] is what decides the UBSan guards 0x7f158 / 0x7f188 / 0x7f1c4
   (`bgeu s11,cur+k` with s11 = 1, k = 1, 2, 3: decide_cond's ranges_ltu, Reusable/YP0m.v:647-652, 698-708); the
   countdown has [1, 4096] where the asan state's i has [0, 4095] *)
Definition rl_atomsR (nrem ncur ncnt nd nh nnow nq : nat) : list (nat * afact) :=
[(nrem, mkAF 0 67108863 0); (ncur, mkAF 4096 140737479966720 0); (ncnt, mkAF 1 4096 0);
(nd, mkAF 0 1 0); (nh, mkAF 0 1 0);
(nnow, mkAF 0 9223406396593514176 0); (nq, mkAF 0 9223406396593514176 0)].

(* ===================== the four states [lib/A/APgLoop0.v:428-482] ===================== *)
(* ss_L, pc 0x7f154: the loop head, after `beqz s9,0x7f2c4` at 0x7f150 *)
Definition ss_L_0 : sstate :=
mkSS 0x7f154
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
SOff N_h 0; SOff N_cur 0; SOff 75 32; SOff N_now 0; SOff 88 0; SOff 23 0; SOff N_d 0; SOff N_rem 0;
SOff N_cnt 0; SLit 1; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
(rl_mem N_st N_p1 N_op N_due N_hns N_g N_p2 N_quiet)
None
(mkFacts (rl_atoms0 ++ rl_atomsK N_st N_op N_due N_hns N_g N_p1 N_p2
++ rl_atomsR N_rem N_cur N_cnt N_d N_h N_now N_quiet) [] rl_alias).
Definition ss_L : sstate := Eval vm_compute in ss_havoc_regs ss_L_0 RT_LN rt_loop_deads7.

(* ss_T, pc 0x7f1ec: the one to three input bytes are read. a1 = the low byte, a2 = 256 * the high byte,
   s7 = ev, s3 = cur', s9 = rem'. *)
Definition ss_T_0 : sstate :=
mkSS 0x7f1ec
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
SOff 10 0; SOff N_lo 0; SOff N_hi 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
SOff N_h 0; SOff N_curT 0; SOff 75 32; SOff N_now 0; SOff 88 0; SOff N_ev 0; SOff N_d 0; SOff N_remT 0;
SOff N_cnt 0; SLit 1; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
(rl_mem N_st N_p1 N_op N_due N_hns N_g N_p2 N_quiet)
None
(mkFacts (rl_atoms0 ++ rl_atomsK N_st N_op N_due N_hns N_g N_p1 N_p2
++ rl_atomsR N_remT N_curT N_cnt N_d N_h N_now N_quiet
++ [(N_ev, mkAF 0 255 0); (N_lo, mkAF 0 255 0); (N_hi, mkAF 0 65280 0)]) [] rl_alias).
Definition ss_T : sstate := Eval vm_compute in ss_havoc_regs ss_T_0 RT_TN rt_loop_deadsT.

(* ss_M, pc 0x7f21c: after `now += dt << sh` and the optional HEARD call *)
Definition ss_M_0 : sstate :=
mkSS 0x7f21c
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
SOff N_hM 0; SOff N_curT 0; SOff 75 32; SOff N_nowM 0; SOff 88 0; SOff N_ev 0; SOff N_d 0; SOff N_remT 0;
SOff N_cnt 0; SLit 1; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
(rl_mem N_stM N_p1 N_op N_due N_hnsM N_g N_p2 N_quietM)
None
(mkFacts (rl_atoms0 ++ rl_atomsK N_stM N_op N_due N_hnsM N_g N_p1 N_p2
++ rl_atomsR N_remT N_curT N_cnt N_d N_hM N_nowM N_quietM
++ [(N_ev, mkAF 0 255 0)]) [] rl_alias).
Definition ss_M : sstate := Eval vm_compute in ss_havoc_regs ss_M_0 RT_MN rt_loop_deads.

(* ss_C, pc 0x7f270: after the optional STEP call and its four aborts *)
Definition ss_C_0 : sstate :=
mkSS 0x7f270
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
SOff N_hM 0; SOff N_curT 0; SOff 75 32; SOff N_nowM 0; SOff 88 0; SOff 23 0; SOff N_dC 0; SOff N_remT 0;
SOff N_cnt 0; SLit 1; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
(rl_mem N_stC N_p1 N_op N_dueC N_hnsM N_gC N_p2 N_quietM)
None
(mkFacts (rl_atoms0 ++ rl_atomsK N_stC N_op N_dueC N_hnsM N_gC N_p1 N_p2
++ rl_atomsR N_remT N_curT N_cnt N_dC N_hM N_nowM N_quietM) [] rl_alias).
Definition ss_C : sstate := Eval vm_compute in ss_havoc_regs ss_C_0 RT_CN rt_loop_deads7.

(* ===================== structural facts ===================== *)
(* the pcs of the cut *)
Lemma ss_pcs : ss_pc ss_L = 0x7f154 /\ ss_pc ss_T = 0x7f1ec /\ ss_pc ss_M = 0x7f21c /\ ss_pc ss_C = 0x7f270 /\
ss_pc ss_X = 0x7f2c4.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* one symbolic value per register *)
Lemma ss_regs_len : length (ss_regs ss_L) = 32%nat /\ length (ss_regs ss_T) = 32%nat /\
length (ss_regs ss_M) = 32%nat /\ length (ss_regs ss_C) = 32%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the region lists are well formed (st_ok's first memory conjunct, YP09.regions_wf) *)
Lemma ss_regions_wf : regions_wf (ss_mem ss_L) = true /\ regions_wf (ss_mem ss_T) = true /\
regions_wf (ss_mem ss_M) = true /\ regions_wf (ss_mem ss_C) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the three body states and the head share one memory shape, up to the slots of k's cells and quiet *)
Lemma ss_mem_shapes :
ss_mem ss_L = rl_mem N_st N_p1 N_op N_due N_hns N_g N_p2 N_quiet /\
ss_mem ss_T = rl_mem N_st N_p1 N_op N_due N_hns N_g N_p2 N_quiet /\
ss_mem ss_M = rl_mem N_stM N_p1 N_op N_due N_hnsM N_g N_p2 N_quietM /\
ss_mem ss_C = rl_mem N_stC N_p1 N_op N_dueC N_hnsM N_gC N_p2 N_quietM.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the joins into ss_X: S6's exits 0x7f29c (j, after `bnez s10` falls through) and 0x7f150 (`beqz s9`), and S2's
   exit 0x7f150, are taken from ss_C / ss_L-shaped memory; submem_to closes both, as lib/A/APgLoop0.v:568-570 says of
   the asan states *)
Lemma ss_X_sub_C : submem (ss_mem ss_X) (ss_mem ss_C).
Proof. unfold ss_X, ss_C. cbn [ss_mem]. submem_to. Qed.
Lemma ss_X_sub_L : submem (ss_mem ss_X) (ss_mem ss_L).
Proof. unfold ss_X, ss_L. cbn [ss_mem]. submem_to. Qed.

(* ===================== the exit segment at this library's context record =====================
   a Theorem Labs lane's S7 EXIT (lib/AU/APgMain7.v rt_X) is stated over lib/AU/APgRt.v's context record itself: APgMain7 no
   longer takes the record as Section variables with one equation each, so rt_X IS the lemma at this record and
   rt_X_at_rt only names it. The implicit FPState / RunCeil / sink_head arguments are passed by name. *)
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma rt_X_at_rt (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) :
ameter_laws MT -> TfibLib B -> AR_laws tfibsegs B -> model_laws (as_universe B) -> astack_free_law tfibsegs B ->
frame_flag_lawP tfibsegs B -> ameter_fs_laws MT ->
@APgRt.rt_from fx rc SK B MT FP (@APgRt.rt_post fx rc SK B MT FP) ss_X (INV_X B MT).
Proof.
intros MTL TL LAWS ML ASF FFL MTF.
exact (@APgMain7.rt_X fx rc SK B MT FP MTL TL LAWS ML ASF FFL MTF).
Qed.
End x.

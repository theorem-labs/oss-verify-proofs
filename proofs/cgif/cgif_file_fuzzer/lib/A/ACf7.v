(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l ACej ACeh ACem ACek ACei ACer ACfm ACf5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACf9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Definition ss_A2 : sstate :=
(mkSS 525832 [SLit 0; SOff 71 0; SOff 70 0; SOff 3 0; SOff 4 0;  SOff 72 0; SOff 73 0; SOff 74 0; SOff 2 0; SOff 70 0; SLit 18446744073709551608; SLit 18446744073709551603; SLit 95663; SLit 525456; SOff 79 0; SOff 80 0; SOff 81 0; SOff 82 0; SOff 75 0;  SOff 11 0; SOff 75 32; SOff 10 0;  SOff 88 0; SOff 75 0; SOff 32 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 83 0; SOff 84 0;  SOff 85 0; SOff 86 0] [{| r_base := Some 88%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [{| c_off := 15; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 17; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 23; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 22; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 21; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 20; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}] |}; {| r_base := Some 75%nat; r_lo := 0; r_hi := 256; r_wlo := 0; r_whi := 256; r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SLit 525456) |}; {| c_off := 8; YP09.c_val := CVal 8 (SLit 95663) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 248; YP09.c_val := CVal 8 (SOff 87 0) |}] |}; {| r_base := Some 70%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [{| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SOff 75 0) |}] |}; {| r_base := Some 2%nat; r_lo := -96; r_hi := 0; r_wlo := -96; r_whi := 0; r_chunks := [{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |}; {| r_base := None; r_lo := 647064; r_hi := 647072; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 647064; YP09.c_val := CVal 8 (SLit 679928) |}] |}; {| r_base := None; r_lo := 679928; r_hi := 679936; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 679928; YP09.c_val := CVal 8 (SOff 32 0) |}] |}; {| r_base := None; r_lo := 647152; r_hi := 647160; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 647152; YP09.c_val := CVal 8 (SLit 679936) |}] |}; {| r_base := None; r_lo := 679936; r_hi := 679940; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 679936; YP09.c_val := CVal 4 (SLit 1) |}] |}] None {| f_atoms := [(88%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (87%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (75%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (70%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (11%nat, {| af_lo := 0; af_hi := 67108863; af_al2 := 0 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |})]; f_conds := []; f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)] |})
.
Definition ss_B : sstate :=
(mkSS 525848 [SLit 0; SOff 89 0; SOff 70 0; SOff 3 0; SOff 4 0;  SOff 90 0; SOff 91 0; SOff 92 0; SOff 2 0; SOff 70 0;  SOff 93 0; SOff 94 0; SOff 95 0; SOff 96 0; SOff 97 0;  SOff 98 0; SOff 99 0; SOff 100 0; SOff 75 0;  SOff 11 0; SOff 75 32; SOff 10 0;  SOff 88 0; SOff 75 0; SOff 32 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 101 0; SOff 102 0;  SOff 103 0; SOff 104 0] [{| r_base := Some 75%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |}; {| r_base := Some 75%nat; r_lo := 32; r_hi := 80; r_wlo := 32; r_whi := 80; r_chunks := [{| c_off := 32; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 48; YP09.c_val := CVal 4 (SLit 0) |}; {| c_off := 52; YP09.c_val := CVal 4 (SLit 0) |}; {| c_off := 56; YP09.c_val := CVal 2 (SLit 0) |}; {| c_off := 58; YP09.c_val := CVal 2 (SLit 0) |}; {| c_off := 60; YP09.c_val := CVal 2 (SLit 0) |}; {| c_off := 62; YP09.c_val := CVal 2 (SLit 0) |}; {| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SLit 0) |}] |}; {| r_base := Some 88%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 15; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 17; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 23; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 22; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 21; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 20; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}] |}; {| r_base := Some 75%nat; r_lo := 80; r_hi := 256; r_wlo := 80; r_whi := 256; r_chunks := [{| c_off := 248; YP09.c_val := CVal 8 (SOff 87 0) |}] |}; {| r_base := Some 70%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [{| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SOff 75 0) |}] |}; {| r_base := Some 2%nat; r_lo := -96; r_hi := 0; r_wlo := -96; r_whi := 0; r_chunks := [{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |}; {| r_base := None; r_lo := 647064; r_hi := 647072; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 647064; YP09.c_val := CVal 8 (SLit 679928) |}] |}; {| r_base := None; r_lo := 679928; r_hi := 679936; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 679928; YP09.c_val := CVal 8 (SOff 32 0) |}] |}; {| r_base := None; r_lo := 647152; r_hi := 647160; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 647152; YP09.c_val := CVal 8 (SLit 679936) |}] |}; {| r_base := None; r_lo := 679936; r_hi := 679940; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 679936; YP09.c_val := CVal 4 (SLit 1) |}] |}] None {| f_atoms := [(88%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (87%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (75%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (70%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (11%nat, {| af_lo := 0; af_hi := 67108863; af_al2 := 0 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |})]; f_conds := []; f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)] |})
.
Fixpoint idx_of' {A} (f : A -> bool) (l : list A) : nat :=
match l with [] => 0%nat | x :: t => if f x then 0%nat else S (idx_of' f t) end.
Definition rt_X_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 19; 21; 24; 26; 25; 28; 29; 30; 31]%nat.
Definition rt_X_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 19; 21; 24; 26; 25; 28; 29; 30; 31]%bv.
Definition RT_XN : nat := 600.
Definition rt_region_by (f : YP09.region -> bool) (rs : smem) : YP09.region := nth (idx_of' f rs) rs got_region.
Definition rt_X_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0;
SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 75 0; SOff 20 0; SOff 19 0; SOff 21 0; SOff 88 0; SOff 75 0; SOff 22 0; SOff 24 0; SOff 23 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ss_X_0 : sstate :=
mkSS 0x80878 rt_X_regs
[ YP09.mkRegion (Some 75%nat) 0 32 0 32 [];
rt_region_by (fun r => match YP09.r_base r with Some 88%nat => true | _ => false end) (ss_mem ss_B);
YP09.mkRegion (Some 75%nat) 240 256 240 256 [YP09.mkChunk 248 (CVal 8 (SOff 87 0))];
rt_region_by (fun r => match YP09.r_base r with Some 2%nat => true | _ => false end) (ss_mem ss_B) ]
None (ss_facts ss_B).
Definition ss_X : sstate := Eval vm_compute in ss_havoc_regs ss_X_0 RT_XN rt_X_deads.
Definition INV_XP (B : asyms) (MT : ameter_ops) (PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= EV_LIB /\ acc <= c_T cx /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\ PX ly3 (ablocks B ly3 S3) W3 (ms_mem ms3) md3.
Definition INV_X (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx => INV_XP B MT (fun _ _ _ _ _ => hdr_fail cx) cx.
Definition rt_chunk_redesc (off : Z) (e : sv) (c : YP09.chunk) : YP09.chunk :=
if Z.eqb (YP09.c_off c) off then match YP09.c_val c with CVal w _ => YP09.mkChunk off (CVal w e) | _ => c end else c.
Definition rt_rechunk (s : sstate) (base : nat) (off : Z) (e : sv) : sstate :=
ss_set_mem s (map (fun r => match YP09.r_base r with
| Some b => if Nat.eqb b base then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(map (rt_chunk_redesc off e) (YP09.r_chunks r)) else r
| None => r end) (ss_mem s)).
Definition rt_clear_conds (s : sstate) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts (f_atoms (ss_facts s)) [] (f_alias (ss_facts s))).
Definition rt_Bend0 : sstate :=
(mkSS 526340 [SLit 0; SOff 169 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 170 0; SOff 171 0; SOff 172 0; SOff 2 0; SOff 70 0; SOff 173 0; SAlu ALU_AND (SExt false 8 (SOff 185 0)) (SLit 4); SOff 175 0; SOff 176 0; SOff 177 0; SOff 178 0;  SOff 179 0; SOff 180 0; SOff 75 0; SOff 75 56; SOff 75 32; SOff 75 58; SOff 88 0; SOff 75 0; SAlu ALU_OR (SAlu ALU_OR (SOff 125 0) (SOff 109 0)) (SAlu ALU_OR (SOff 141 0) (SOff 157 0)); SOff 141 0; SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_OR (SOff 125 0) (SOff 109 0)) (SAlu ALU_OR (SOff 141 0) (SOff 157 0))) (SOff 173 0); SOff 27 0; SOff 181 0; SOff 182 0; SOff 183 0; SOff 184 0] [{| r_base := Some 75%nat; r_lo := 32; r_hi := 80; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 32; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 48; YP09.c_val := CVal 4 (SOff 185 0) |}; {| c_off := 52; YP09.c_val := CVal 4 (SOff 186 0) |}; {| c_off := 56; YP09.c_val := CVal 2 (SOff 187 0) |}; {| c_off := 58; YP09.c_val := CVal 2 (SOff 188 0) |}; {| c_off := 60; YP09.c_val := CVal 2 (SOff 189 0) |}; {| c_off := 62; YP09.c_val := CVal 2 (SLit 0) |}; {| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SLit 0) |}] |}; {| r_base := Some 75%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |}; {| r_base := Some 88%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 15; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 17; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 23; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 22; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 21; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 20; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}] |}; {| r_base := Some 75%nat; r_lo := 80; r_hi := 256; r_wlo := 80; r_whi := 256; r_chunks := [{| c_off := 248; YP09.c_val := CVal 8 (SOff 87 0) |}] |}; {| r_base := Some 2%nat; r_lo := -96; r_hi := 0; r_wlo := -96; r_whi := 0; r_chunks := [{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |}; {| r_base := None; r_lo := 647064; r_hi := 647072; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 647064; YP09.c_val := CVal 8 (SLit 679928) |}] |}; {| r_base := None; r_lo := 679928; r_hi := 679936; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 679928; YP09.c_val := CVal 8 (SOff 32 0) |}] |}; {| r_base := None; r_lo := 647152; r_hi := 647160; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 647152; YP09.c_val := CVal 8 (SLit 679936) |}] |}; {| r_base := None; r_lo := 679936; r_hi := 679940; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 679936; YP09.c_val := CVal 4 (SLit 1) |}] |}] None {| f_atoms := [(185%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (186%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (187%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (188%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (189%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (88%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (87%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (75%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (70%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (11%nat, {| af_lo := 0; af_hi := 67108863; af_al2 := 0 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |})]; f_conds := [{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SExt false 8 (SOff 185 0)) (SLit 4); ac_b := SLit 0 |}]; f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)] |})
.
Definition rt_Bend_deads : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 26; 28; 29; 30; 31]%nat.
Definition rt_Bend_deads_bv : list (bv 5) := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 26; 28; 29; 30; 31]%bv.
Definition rt_Bend_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
SAlu ALU_AND (SExt false 8 (SOff 185 0)) (SLit 4); SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
SOff 75 0; SOff 11 0; SOff 75 32; SOff 10 0; SOff 88 0; SOff 75 0; SOff 190 0; SOff 193 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition rt_obj_region : YP09.region :=
YP09.mkRegion (Some 70%nat) 0 32 0 32 [YP09.mkChunk 24 (CVal 8 (SOff 193 0)); YP09.mkChunk 16 (CVal 8 (SOff 11 0));
YP09.mkChunk 8 (CVal 8 (SOff 10 0)); YP09.mkChunk 0 (CVal 8 (SOff 75 0))].
Definition ss_Bend : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x80804 rt_Bend_regs (rt_obj_region :: ss_mem rt_Bend0) None
(mkFacts (f_atoms (ss_facts rt_Bend0)) [] (f_alias (ss_facts rt_Bend0)))) 160 rt_Bend_deads.
Definition rt_drop_obj (s : sstate) : sstate :=
ss_set_mem s (List.filter (fun r => match YP09.r_base r with Some 70%nat => false | _ => true end) (ss_mem s)).
Definition rt_C_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 25; 28; 29; 30; 31; 26]%nat.
Definition rt_C_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 25; 28; 29; 30; 31; 26]%bv.
Definition rt_C0_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 28; 29; 30; 31]%nat.
Definition rt_C0_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 28; 29; 30; 31]%bv.
Definition ss_C : sstate := Eval vm_compute in
rt_clear_conds (ss_set_pc (ss_havoc_regs ss_Bend 400 rt_C0_deads) 0x80808).
Definition ss_D : sstate := Eval vm_compute in
rt_clear_conds (ss_set_pc (ss_set_regs (rt_rechunk (rt_drop_obj (ss_havoc_regs ss_Bend 400 rt_C_deads)) 75 32 (SOff 191 0)) [(24%nat, SOff 192 0)]) 0x80854).
Definition rt_gc (nr : nat) (cx : rtcx) (E : env) (W3 : world tfibsegs) (ms3 : machine_state) (attr gen w16 h16 ngp cur r : Z) : Prop :=
ew E 185 = Z_to_bv 64 attr /\ ew E 186 = Z_to_bv 64 gen /\ ew E 187 = Z_to_bv 64 w16 /\ ew E 188 = Z_to_bv 64 h16 /\ ew E 189 = Z_to_bv 64 ngp /\
ew E nr = Z_to_bv 64 r /\
0 <= attr < 2 ^ 32 /\ 0 <= gen < 2 ^ 32 /\ 0 <= w16 < 65536 /\ 0 <= h16 < 65536 /\ 0 <= ngp < 65536 /\ 0 <= cur <= c_n cx /\ 0 <= r < 2 ^ 64 /\
(r = 0 -> 14 <= c_n cx) /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8) 8 (c_p cx) /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8 + 8) 8 (c_n cx) /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8 + 16) 8 cur /\
(r = 0 -> hdr_prov cx attr gen w16 h16 ngp) /\
(r <> 0 -> c_n cx < 14 \/ (Z.land attr 4 = 0 /\ hdr_prov cx attr gen w16 h16 ngp /\ c_n cx < 14 + 3 * ngp)).
Lemma rt_gc_havoc : forall nr cx E W3 ms3 N vs attr gen w16 h16 ngp cur r, (193 <= N)%nat -> (nr < 193)%nat ->
rt_gc nr cx E W3 ms3 attr gen w16 h16 ngp cur r -> rt_gc nr cx (havoc E N vs) W3 ms3 attr gen w16 h16 ngp cur r.
Proof. intros nr cx E W3 ms3 N vs attr gen w16 h16 ngp cur r HN Hr H. unfold rt_gc in *. rewrite !ew_havoc_old by lia. exact H. Qed.
Lemma rt_gc_ewset : forall nr cx E W3 ms3 N v attr gen w16 h16 ngp cur r, (193 <= N)%nat -> (nr < 193)%nat ->
rt_gc nr cx E W3 ms3 attr gen w16 h16 ngp cur r -> rt_gc nr cx (ewset E N v) W3 ms3 attr gen w16 h16 ngp cur r.
Proof. intros nr cx E W3 ms3 N v attr gen w16 h16 ngp cur r HN Hr H. unfold rt_gc in *. rewrite !ew_ewset_other by lia. exact H. Qed.
Definition INV_C (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 0 /\ acc <= ACC0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
exists attr gen w16 h16 ngp cur r, rt_gc 190 cx E W3 ms3 attr gen w16 h16 ngp cur r /\ Z.land attr 4 = 0 /\
(r = 0 -> cur = 14) /\ ew E 193 = Z_to_bv 64 cur.
Definition INV_Bend (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 0 /\ acc <= ACC0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
exists attr gen w16 h16 ngp cur r, rt_gc 190 cx E W3 ms3 attr gen w16 h16 ngp cur r /\
(r = 0 -> cur = 14) /\ ew E 193 = Z_to_bv 64 cur.
Definition rt_newblk (B : asyms) (FP : list (Z * Z)) (cx : rtcx) (b n : Z) (ly3 : alayout) (S3 : astate) : Prop :=
(4096 <= b /\ zone2 b (req_size n)) /\ b + req_size n <= alloc_ceiling /\ b mod 16 = 0 /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(b, n)] /\
(forall blc lyq ownq i, In (b, n) blc -> 0 <= i < req_size n ->
awr_byte LLVMF_STK (spZ (c_regs cx)) FP (ablocks B (c_ly cx) (c_S cx)) blc lyq ownq (b + i)) /\
aftok FP (ablocks B (c_ly cx) (c_S cx)) (b, n).
Definition rt_palD (B : asyms) (FP : list (Z * Z)) (cx : rtcx) (attr pal ngp cur r : Z) (ly3 : alayout) (S3 : astate) (m : word -> option byte) : Prop :=
(Z.land attr 4 <> 0 /\ pal = 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\ (r = 0 -> cur = 14)) \/
(Z.land attr 4 = 0 /\ pal <> 0 /\ rt_newblk B FP cx pal (3 * ngp) ly3 S3 /\
(r = 0 -> cur = 14 + 3 * ngp /\ pal_prov cx pal ngp m)).
Lemma rt_palD_kept : forall B FP cx attr pal ngp cur r ly3 S3 H (m m' : word -> option byte),
(pal <> 0 -> forall i, 0 <= i < 3 * ngp -> aview tfibsegs H m' (pal + i) = aview tfibsegs H m (pal + i)) ->
rt_palD B FP cx attr pal ngp cur r ly3 S3 (mrestrict H m) -> rt_palD B FP cx attr pal ngp cur r ly3 S3 (mrestrict H m').
Proof.
intros B FP cx attr pal ngp cur r ly3 S3 H m m' Hv [HL | (Ha & Hp & Hnb & Hpp)]; [left; exact HL | right].
split; [exact Ha|]. split; [exact Hp|]. split; [exact Hnb|]. intros Hr. destruct (Hpp Hr) as [Hc Hpv]. split; [exact Hc|].
intros i Hi. destruct (Hpv i Hi) as (b & Hb & Hval). exists b. split; [exact Hb|].
eapply rt_val_mem_frame; [|exact Hval]. intros x Hx. cbn in Hx. replace x with (pal + i) by lia.
apply (mbyte_of_aview tfibsegs). apply (Hv Hp i Hi).
Qed.
Lemma rt_palD_r0 : forall B FP cx attr pal ngp cur r ly3 S3 m,
r = 0 -> rt_palD B FP cx attr pal ngp cur r ly3 S3 m -> rt_palD B FP cx attr pal ngp cur 0 ly3 S3 m.
Proof. intros B FP cx attr pal ngp cur r ly3 S3 m -> H. exact H. Qed.
Definition INV_D (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 1 /\ acc <= ACC_pal MT /\
exists attr gen w16 h16 ngp cur r pal, rt_gc 192 cx E W3 ms3 attr gen w16 h16 ngp cur r /\ ew E 191 = Z_to_bv 64 pal /\ 0 <= pal < 2 ^ 64 /\
rt_palD B FP cx attr pal ngp cur r ly3 S3 (mrestrict (w_H W3) (ms_mem ms3)).
Definition INV_Dx (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
(bv_unsigned (ew E 192) = 0 -> 100000000 < bv_unsigned (ew E 187) * bv_unsigned (ew E 188)) /\
INV_D B MT FP cx E k acc ly3 S3 W3 ms3 md3.
Definition rt_Dx_deads_bv : list (bv 5) := [10; 11; 19]%bv.
Definition rt_E_deads_bv : list (bv 5) := [10; 11]%bv.
Definition ss_Dx : sstate := Eval vm_compute in rt_clear_conds (ss_set_pc (ss_havoc_regs ss_D 420 [10; 11; 19]%nat) 0x80870).
Definition rt_D0 : sstate := Eval vm_compute in
rt_clear_conds (ss_set_pc (ss_set_regs (rt_rechunk (ss_havoc_regs rt_Bend0 400 [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 25; 28; 29; 30; 31]%nat) 75 32 (SOff 191 0)) [(26%nat, SOff 192 0)]) 0x80854).
Definition ss_E : sstate := Eval vm_compute in
ss_set_regs (rt_clear_conds (ss_set_facts (ss_set_pc (ss_set_regs (ss_havoc_regs rt_D0 420 [10; 11]%nat) [(19%nat, SOff 194 0)]) 0x809e4)
(f_atoms (ss_facts rt_D0) ++ [(194%nat, mkAF 0 100000000 0)]))) [(21%nat, SOff 10 0); (26%nat, SOff 418 0)].
Definition INV_E (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 1 /\ acc <= ACC_pal MT /\
exists attr gen w16 h16 ngp cur pal, rt_gc 192 cx E W3 ms3 attr gen w16 h16 ngp cur 0 /\
ew E 194 = Z_to_bv 64 (w16 * h16) /\ w16 * h16 <= 100000000 /\ ew E 191 = Z_to_bv 64 pal /\ 0 <= pal < 2 ^ 64 /\
rt_palD B FP cx attr pal ngp cur 0 ly3 S3 (mrestrict (w_H W3) (ms_mem ms3)).
Definition rt_F_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 24; 26; 25; 28; 29; 30; 31]%nat.
Definition rt_F_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 24; 26; 25; 28; 29; 30; 31]%bv.
Definition rt_F_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0;
SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 75 0; SOff 194 0; SOff 195 0; SOff 21 0; SOff 88 0; SOff 75 0; SOff 22 0; SOff 24 0; SOff 23 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ss_F_0 : sstate :=
mkSS 0x80a0c rt_F_regs
(List.filter (fun r => match YP09.r_base r with Some 75%nat => negb (Z.eqb (YP09.r_lo r) 32) | _ => true end) (ss_mem ss_E))
None (mkFacts (f_atoms (ss_facts ss_B) ++ [(194%nat, mkAF 0 100000000 0)]) [] (f_alias (ss_facts ss_B))).
Definition ss_F : sstate := Eval vm_compute in ss_havoc_regs ss_F_0 200 rt_F_deads.
Definition rt_obj (B : asyms) (cx : rtcx) (E : env) (ly3 : alayout) (S3 : astate) (W3 : world tfibsegs) (ms3 : machine_state)
(g : Z) (s : cgif_st) (N cur : Z) (extra : list (Z * Z)) : Prop :=
ew E 195 = Z_to_bv 64 g /\ ew E 194 = Z_to_bv 64 N /\ 0 <= cur <= c_n cx /\ 14 <= c_n cx /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8) 8 (c_p cx) /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8 + 8) 8 (c_n cx) /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8 + 16) 8 cur /\
tcgif_at (mrestrict (w_H W3) (ms_mem ms3)) g s /\ cgif_wf s N /\
Permutation (ablocks B ly3 S3) ((cgif_blocks g s N ++ extra) ++ ablocks B (c_ly cx) (c_S cx)).
Definition INV_F (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 14 /\ acc <= c_T cx /\ exists g s N cur, rt_obj B cx E ly3 S3 W3 ms3 g s N cur [].
End d.
Ltac palv_run HFr Hpal AG keep :=
let L := lazymatch goal with Lw : AR_laws tfibsegs _ |- _ => Lw end in let Hv := fresh "Hpalv" in
lazymatch type of Hpal with rt_palD ?Bv _ _ _ ?pal ?ngp _ _ ?ly3 ?S3 _ =>
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wv) ?m0) (mrestrict _ ?m1) =>
lazymatch goal with HAR3x : AR _ Bv ly3 S3 ?W3 ?mm3 ?md3, Hfinx : In (2, ?fpos) (frames S3) |- _ =>
assert (Hv : pal <> 0 -> forall i, 0 <= i < 3 * ngp -> aview tfibsegs (w_H Wv) m1 (pal + i) = aview tfibsegs (w_H Wv) m0 (pal + i));
[ let Hp1 := fresh "Hp1" in let i := fresh "i" in let Hi := fresh "Hi" in
let Hbh := fresh "Hbh" in let Hbz := fresh "Hbz" in let Hbc := fresh "Hbc" in let Eabp := fresh "Eabp" in let Hpin3 := fresh "Hpin3" in let HdFPp := fresh "HdFPp" in
intros Hp1 i Hi;
destruct Hpal as [(_ & Hp0' & _) | (_ & _ & (([Hbh Hbz] & Hbc & _ & Eabp & _ & _) & _))]; [exfalso; exact (Hp1 Hp0')|];
pose proof (le_req_size (3 * ngp) ltac:(lia)) as Hrq1p;
assert (Hpin3 : In (pal, 3 * ngp) (ablocks Bv ly3 S3)) by (rewrite Eabp; apply in_app_iff; right; left; reflexivity);
pose proof (sep_block_frame tfibsegs _ L ly3 S3 _ _ _ pal (3 * ngp) 2 fpos HAR3x Hpin3 Hfinx) as HdFPp;
unfold zdisjoint in HdFPp; cbn [fst snd] in HdFPp; change (fs_frame_bytes 2) with 256 in HdFPp;
try match goal with EFAx : forall c q, frame_addr ly3 c q = frame_addr _ c q |- _ => rewrite EFAx in HdFPp end;
try match goal with Fx := frame_addr _ 2 fpos |- _ => fold Fx in HdFPp end;
apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by (revert Hi Hbh Hbc Hrq1p; keep; pose proof (proj1 asan_consts); intros; lia);
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first [ revert Hrg Hi Hbh Hbz Hbc Hrq1p HdFPp; keep; intros Hrg Hi Hbh Hbz Hbc Hrq1p HdFPp;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia
| match goal with |- ?g => idtac "PALV-FAIL" g end ]
|]);
destruct Hin
| ] end end end.
Ltac imgv_run HFr AG keep :=
let Hv := fresh "Himgv" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wv) ?m0) (mrestrict _ ?m1) =>
assert (Hv : forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wv) m1 a = aview tfibsegs (w_H Wv) m0 a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Har := fresh "Har" in
intros a Ha; pose proof (tfib_img_range a Ha) as Har;
apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by (clear - Har; lia);
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first [ revert Hrg Har; keep; intros Hrg Har; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia
| match goal with |- ?g => idtac "IMGV-FAIL" g end ]
|]);
destruct Hin
| ] end.

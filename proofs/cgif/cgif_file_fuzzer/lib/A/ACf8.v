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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l ACej ACeh ACem ACek ACei ACer ACfm ACf5 ACf7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Definition rt_G_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 25; 28; 29; 30; 31]%nat.
Definition rt_G_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 25; 28; 29; 30; 31]%bv.
Definition rt_fconfig_region : YP09.region :=
{| r_base := Some 75%nat; r_lo := 112; r_hi := 144; r_wlo := 112; r_whi := 144;
r_chunks := [{| c_off := 112; YP09.c_val := CVal 8 (SOff 402 0) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 403 0) |};
{| c_off := 128; YP09.c_val := CVal 4 (SOff 404 0) |}; {| c_off := 132; YP09.c_val := CVal 4 (SOff 405 0) |};
{| c_off := 136; YP09.c_val := CVal 2 (SOff 406 0) |}; {| c_off := 138; YP09.c_val := CVal 2 (SOff 407 0) |};
{| c_off := 140; YP09.c_val := CVal 1 (SOff 408 0) |}] |}.
Definition rt_frame_hi : YP09.region :=
{| r_base := Some 75%nat; r_lo := 144; r_hi := 256; r_wlo := 144; r_whi := 256; r_chunks := [{| c_off := 248; YP09.c_val := CVal 8 (SOff 87 0) |}] |}.
Definition rt_frame_lo : YP09.region := {| r_base := Some 75%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |}.
Definition rt_shadow_region : YP09.region := nth 1 (ss_mem ss_F) got_region.
Definition rt_stack_region : YP09.region := nth 3 (ss_mem ss_F) got_region.
Definition rt_const_regions : smem := skipn 4 (ss_mem ss_F).
Definition rt_G_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0;
SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 75 0; SOff 194 0; SOff 195 0; SOff 75 112; SOff 88 0; SOff 75 0; SOff 400 0; SOff 24 0; SOff 23 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ss_G_0 : sstate :=
mkSS 0x80a28 rt_G_regs (rt_fconfig_region :: rt_frame_lo :: rt_shadow_region :: rt_frame_hi :: rt_stack_region :: rt_const_regions)
None (ss_facts ss_F).
Definition ss_G : sstate := Eval vm_compute in ss_havoc_regs ss_G_0 410 rt_G_deads.
Definition rt_objG (B : asyms) (cx : rtcx) (E : env) (ly3 : alayout) (S3 : astate) (W3 : world tfibsegs) (ms3 : machine_state)
(g : Z) (s : cgif_st) (N : Z) (extra : list (Z * Z)) : Prop :=
ew E 195 = Z_to_bv 64 g /\ ew E 194 = Z_to_bv 64 N /\ 14 <= c_n cx /\
tcgif_at (mrestrict (w_H W3) (ms_mem ms3)) g s /\ cgif_wf s N /\
Permutation (ablocks B ly3 S3) ((cgif_blocks g s N ++ extra) ++ ablocks B (c_ly cx) (c_S cx)).
Definition rt_stm (cx : rtcx) (W3 : world tfibsegs) (ms3 : machine_state) (cur : Z) : Prop :=
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8) 8 (c_p cx) /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8 + 8) 8 (c_n cx) /\
val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 8 + 16) 8 cur /\ 0 <= cur <= c_n cx.
Definition rt_fcfg (E : env) (lpal lpa img fattr fgen delay nlp tidx : Z) : Prop :=
ew E 402 = Z_to_bv 64 lpal /\ ew E 403 = Z_to_bv 64 img /\ ew E 404 = Z_to_bv 64 fattr /\ ew E 405 = Z_to_bv 64 fgen /\
ew E 406 = Z_to_bv 64 delay /\ ew E 407 = Z_to_bv 64 nlp /\ ew E 408 = Z_to_bv 64 tidx /\
0 <= lpal < 2 ^ 64 /\ 0 <= img < 2 ^ 64 /\ 0 <= fattr < 2 ^ 32 /\ 0 <= fgen < 2 ^ 32 /\ 0 <= delay < 65536 /\ 0 <= nlp < 65536 /\ 0 <= tidx < 256 /\
(Z.land fattr 1 = 0 -> lpal = 0) /\ Z_to_bv 64 lpa = Z_to_bv 64 lpal.
Definition rt_fblocks (img N fattr lpa nlp : Z) : list (Z * Z) := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]).
Definition INV_GX (B : asyms) (MT : ameter_ops) (kb c : Z) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= kb /\ acc <= c_T cx /\ 1 <= c <= 16 /\ ew E 400 = Z_to_bv 64 c /\
exists g s N cur lpal lpa img fattr fgen delay nlp tidx,
rt_objG B cx E ly3 S3 W3 ms3 g s N (rt_fblocks img N fattr lpa nlp) /\ rt_stm cx W3 ms3 cur /\ rt_fcfg E lpal lpa img fattr fgen delay nlp tidx.
Definition INV_G (B : asyms) (MT : ameter_ops) (c : Z) := INV_GX B MT (20 + (16 - c) * 55) c.
Definition INV_G2 (B : asyms) (MT : ameter_ops) (c : Z) := INV_GX B MT (67 + (16 - c) * 55) c.
Definition ss_G2 : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_G 0x80a34) 450 rt_G_deads.
Definition ss_G3 : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_G 0x80a44) 500 rt_G_deads.
Definition INV_G3 (B : asyms) (MT : ameter_ops) (c : Z) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 69 + (16 - c) * 55 /\ acc <= c_T cx /\ 1 <= c <= 16 /\ ew E 400 = Z_to_bv 64 c /\
exists g s N cur, rt_objG B cx E ly3 S3 W3 ms3 g s N [] /\ rt_stm cx W3 ms3 cur.
Definition rt_H_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 24; 26; 25; 28; 29; 30; 31]%nat.
Definition rt_H_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 24; 26; 25; 28; 29; 30; 31]%bv.
Definition rt_H_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0;
SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 75 0; SOff 20 0; SOff 195 0; SOff 21 0; SOff 88 0; SOff 75 0; SOff 22 0; SOff 24 0; SOff 23 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ss_H_0 : sstate :=
mkSS 0x80a60 rt_H_regs (rt_frame_lo :: rt_shadow_region :: rt_frame_hi :: rt_stack_region :: rt_const_regions) None (ss_facts ss_F).
Definition ss_H : sstate := Eval vm_compute in ss_havoc_regs ss_H_0 260 rt_H_deads.
Definition INV_H (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 900 /\ acc <= c_T cx /\
exists g s N leak, rt_objG B cx E ly3 S3 W3 ms3 g s N leak /\ (leak = [] \/ exists a m, leak = [(a, m)] /\ 0 <= m < 3 * 2 ^ 16).
End b.

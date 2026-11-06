(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X0ae X0ab.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110 X10x.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma ps_tail : forall (A G D st fill ret uns v nx usp lo : Z) (loc : list cell)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 c3 c4 : word) F fc (m : mem),
cells_size loc = 48%nat ->
rw_cells bsegs m (usp + -96) (loc ++ [C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra]) -> stk bsegs m lo (usp + -96) -> lo <= usp + -96 ->
rw_cells bsegs m A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 ret); C4 (Z_to_bv 64 uns); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
A + 32 <= lo -> 0 < A -> 0 <= D -> D + fill < 2^63 -> 0 <= ret -> ret < fill < 2^31 ->
((v = 0 /\ nx = D + fill) \/ (v = nx /\ D + ret < nx < D + fill)) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (D + ret - nx)) a1' a2 a3 a4 a5 a6 a7 c2 c3 c4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -96, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (nx - D)); C4 (Z_to_bv 64 uns); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
(MS (mkR (Z_to_bv 64 RA_ps_memchr) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (D + ret)) (Z_to_bv 64 (fill - ret)) (Z_to_bv 64 D) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_ps_memchr)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SZ FR ST LO SY ALO A0 D0 DF R0 RF CASE MI.
unfold RA_ps_memchr.
replace (ret_pc (Z_to_bv 64 0xc1924)) with (Z_to_bv 64 0xc1924) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -96, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
apply rw_cells_app in FR. destruct FR as [FRl FR]. rewrite SZ in FR.
replace (usp + -96 + Z.of_nat 48) with (usp + -48) in FR by lia.
destruct CASE as [(-> & ->)|(-> & NX)].
-
astep. astep. rewrite (sx32_lit fill) by (unfold int31; lia). astep.
astep. rewrite (swrap32_small (D + fill - D)) by lia. replace (D + fill - D) with fill by lia.
ato 0xc1990.
replace (usp + -48) with (usp + -96 + Z.of_nat (cells_size loc)) in FR by lia.
pose proof (rw_cells_join _ _ _ _ _ FRl FR) as FR2. clear FRl FR.
pose proof (stk_release _ _ _ _ _ ST FR2 ltac:(lia)) as ST2. clear ST FR2.
rewrite cells_size_app, SZ in ST2. cbn [cells_size csize Nat.add] in ST2.
replace (usp + -96 + Z.of_nat 96) with usp in ST2 by lia.
astep. astep.
apply evt_done. do 2 eexists. split; [do 3 f_equal; lia|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
replace (D + fill - D) with fill by lia. exact SY.
-
astep. sh_if.
astep. rewrite (swrap32_small (nx - D)) by lia.
ato 0xc1990.
replace (usp + -48) with (usp + -96 + Z.of_nat (cells_size loc)) in FR by lia.
pose proof (rw_cells_join _ _ _ _ _ FRl FR) as FR2. clear FRl FR.
pose proof (stk_release _ _ _ _ _ ST FR2 ltac:(lia)) as ST2. clear ST FR2.
rewrite cells_size_app, SZ in ST2. cbn [cells_size csize Nat.add] in ST2.
replace (usp + -96 + Z.of_nat 96) with usp in ST2 by lia.
astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2| exact SY].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma ps_tail : forall (A G D st fill ret uns v nx usp lo : Z) (loc : list cell)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 c3 c4 : word) F fc (m : mem),
cells_size loc = 48%nat ->
rw_cells asegs m (usp + -96) (loc ++ [C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra]) -> stk asegs m lo (usp + -96) -> lo <= usp + -96 ->
rw_cells asegs m A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 ret); C4 (Z_to_bv 64 uns); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
A + 32 <= lo -> 0 < A -> 0 <= D -> D + fill < 2^63 -> 0 <= ret -> ret < fill < 2^31 ->
((v = 0 /\ nx = D + fill) \/ (v = nx /\ D + ret < nx < D + fill)) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (D + ret - nx)) a1' a2 a3 a4 a5 a6 a7 c2 c3 c4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -96, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 fill); C4 (Z_to_bv 64 (nx - D)); C4 (Z_to_bv 64 uns); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
(MS (mkR (Z_to_bv 64 RA_ps_memchr) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (D + ret)) (Z_to_bv 64 (fill - ret)) (Z_to_bv 64 D) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_ps_memchr)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SZ FR ST LO SY ALO A0 D0 DF R0 RF CASE MI.
unfold RA_ps_memchr.
replace (ret_pc (Z_to_bv 64 0xb91f4)) with (Z_to_bv 64 0xb91f4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. rewrite cells_size_app, SZ in FB. cbn [cells_size csize Nat.add] in FB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -96, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply rw_cells_app in FR. destruct FR as [FRl FR]. rewrite SZ in FR.
replace (usp + -96 + Z.of_nat 48) with (usp + -48) in FR by lia.
destruct CASE as [(-> & ->)|(-> & NX)].
-
astep. astep. rewrite (sx32_lit fill) by (unfold int31; lia). astep.
astep. rewrite (swrap32_small (D + fill - D)) by lia. replace (D + fill - D) with fill by lia.
ato 0xb9260.
replace (usp + -48) with (usp + -96 + Z.of_nat (cells_size loc)) in FR by lia.
pose proof (rw_cells_join _ _ _ _ _ FRl FR) as FR2. clear FRl FR.
pose proof (stk_release _ _ _ _ _ ST FR2 ltac:(lia)) as ST2. clear ST FR2.
rewrite cells_size_app, SZ in ST2. cbn [cells_size csize Nat.add] in ST2.
replace (usp + -96 + Z.of_nat 96) with usp in ST2 by lia.
astep. astep.
apply evt_done. do 2 eexists. split; [do 3 f_equal; lia|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
replace (D + fill - D) with fill by lia. exact SY.
-
astep. sh_if.
astep. rewrite (swrap32_small (nx - D)) by lia.
ato 0xb9260.
replace (usp + -48) with (usp + -96 + Z.of_nat (cells_size loc)) in FR by lia.
pose proof (rw_cells_join _ _ _ _ _ FRl FR) as FR2. clear FRl FR.
pose proof (stk_release _ _ _ _ _ ST FR2 ltac:(lia)) as ST2. clear ST FR2.
rewrite cells_size_app, SZ in ST2. cbn [cells_size csize Nat.add] in ST2.
replace (usp + -96 + Z.of_nat 96) with usp in ST2 by lia.
astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2| exact SY].
Qed.

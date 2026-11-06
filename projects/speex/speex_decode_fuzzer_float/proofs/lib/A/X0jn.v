(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X00b X0jg X0jw X0jt.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X0ra X19x X1ab X1a8.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a8.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x102450, 0x102451); (0x102400, 0x102408); (0x103370, 0x103378);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (flag dso : word),
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800c0000 <= lo ->
ro_cells bsegs m 0xf7f78 [C8 (Z_to_bv 64 0x97744); C8 (Z_to_bv 64 0x44a64)] ->
ro_cells bsegs m 0xfce88 [C8 (Z_to_bv 64 0xf7f88); C8 (Z_to_bv 64 0xf7f78)] ->
ro_cells bsegs m 0xfc0e8 [C8 (Z_to_bv 64 0xe6cc4); C8 (Z_to_bv 64 0)] ->
ro_cells bsegs m 0xfdec8 [C8 dso] ->
ro_cells bsegs m 0xfce00 [C8 (Z_to_bv 64 0x100ab0); C8 (Z_to_bv 64 0x1023f0)] ->
rw_cells bsegs m 0x102450 [C1 (Z_to_bv 8 0)] ->
rw_cells bsegs m 0x102400 [C8 flag] -> bv_unsigned flag <> 0 ->
unreg_got m ->
ro_cells bsegs m 0x1032d0 [C4 (Z_to_bv 64 1)] ->
rw_cells bsegs m 0x103370 [C8 (Z_to_bv 64 0)] ->
ro_cells bsegs m 0x105ab8 [C8 (Z_to_bv 64 0x7fff8000)] ->
rw_cells bsegs m 0x106798 [C1 (Z_to_bv 8 1)] ->
ro_cells bsegs m 0x10531c [C1 (Z_to_bv 8 1)] ->
ro_cells bsegs m 0x197660 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells bsegs m 0xfe040 [C8 (Z_to_bv 64 0xf1af8)] ->
stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
gds_at m 0x100ab0 asan_gds ->
stk bsegs m ODR_LO ODR_HI ->
mem_inv bsegs m ->
evt bsegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6d94) fc None m (seg_rom bsegs)).
Proof.
intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS ODRS MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x102450, 0x102451); (0x102400, 0x102408); (0x103370, 0x103378);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
carve_frame 32%nat ST.
steps_to 0x44a64%Z.

carve_frame 16%nat ST.
steps_to 0x44af0%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.

steps_to 0x97744%Z.
carve_frame 16%nat ST.
steps_to 0x54c74%Z.
carve_frame 16%nat ST.
steps_to 0x5463c%Z.
match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0x100ab0 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
| exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact ODRS| assumption|].
rewrite EU64 in POST. rename POST into ST.
steps_to 0x54cbc%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
steps_to 0x97770%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
steps_to 0xe6ddc%Z. release_frame FR ST (bv_unsigned sp).
astep. astep.
unfold fini_post. sys_finish.
Qed.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0xf9c10, 0xf9c11); (0xf9bc0, 0xf9bc8); (0xfab30, 0xfab38);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (flag dso : word),
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800c0000 <= lo ->
ro_cells asegs m 0xef708 [C8 (Z_to_bv 64 0x97490); C8 (Z_to_bv 64 0x44978)] ->
ro_cells asegs m 0xf4608 [C8 (Z_to_bv 64 0xef718); C8 (Z_to_bv 64 0xef708)] ->
ro_cells asegs m 0xf3868 [C8 (Z_to_bv 64 0xde594); C8 (Z_to_bv 64 0)] ->
ro_cells asegs m 0xf5648 [C8 dso] ->
ro_cells asegs m 0xf4580 [C8 (Z_to_bv 64 0xf8230); C8 (Z_to_bv 64 0xf9bb0)] ->
rw_cells asegs m 0xf9c10 [C1 (Z_to_bv 8 0)] ->
rw_cells asegs m 0xf9bc0 [C8 flag] -> bv_unsigned flag <> 0 ->
unreg_got m ->
ro_cells asegs m 0xfaa90 [C4 (Z_to_bv 64 1)] ->
rw_cells asegs m 0xfab30 [C8 (Z_to_bv 64 0)] ->
ro_cells asegs m 0xfd278 [C8 (Z_to_bv 64 0x7fff8000)] ->
rw_cells asegs m 0xfdf58 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xfcadc [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x18ee20 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xf57c0 [C8 (Z_to_bv 64 0xe9284)] ->
stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
gds_at m 0xf8230 asan_gds ->
stk asegs m ODR_LO ODR_HI ->
mem_inv asegs m ->
evt asegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde664) fc None m (seg_rom asegs)).
Proof.
intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS ODRS MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0xf9c10, 0xf9c11); (0xf9bc0, 0xf9bc8); (0xfab30, 0xfab38);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
carve_frame 32%nat ST.
steps_to 0x44978%Z.

carve_frame 16%nat ST.
steps_to 0x44a04%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.

steps_to 0x97490%Z.
carve_frame 16%nat ST.
steps_to 0x54b88%Z.
carve_frame 16%nat ST.
steps_to 0x54550%Z.
match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0xf8230 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
| exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact ODRS| assumption|].
rewrite EU64 in POST. rename POST into ST.
steps_to 0x54bd0%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
steps_to 0x974bc%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
steps_to 0xde6ac%Z. release_frame FR ST (bv_unsigned sp).
astep. astep.
unfold fini_post. sys_finish.
Qed.


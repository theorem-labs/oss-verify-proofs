(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X00b X0jg X0jw X0jt X0jn.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X0ra X19x X1ab X1a8 X1a2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition exit_prefix_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo code : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR (Z_to_bv 64 0xe6e4c) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xed7ac) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (0x658f08, 0x658f0c); (0x658ce8, 0x658d00); (0x102450, 0x102451);
(0x102400, 0x102408); (0x103370, 0x103378); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
(ODR_LO, ODR_HI)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -16).

Lemma exit_prefix_spec : forall (ph : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word)
(flag dso : word),
a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 0x638c98 -> 0 <= code < 2^64 ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> 0x800c0000 <= lo ->
rw_cells bsegs m 0x638bf0 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
rw_cells bsegs m 0x658ce8 (atexit_cells fin p1 p2 (ph_slot ph) 0x658d00 0 0xe6d8c) ->
atexit_ph ph m ->
rw_cells bsegs m 0x658e08 [C8 (Z_to_bv 64 0x85d14)] ->
rw_cells bsegs m 0x658f08 [C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells bsegs m 0x197960 [C1 (Z_to_bv 8 0)] ->
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
evt bsegs (exit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6de0) fc None m (seg_rom bsegs)).
Proof.
intros until dso. intros -> -> HC ST LO LOLO TID HT ATX PH ATA EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP
THR RMS SC1 SC2 SC3 GDS ODRS MI.
destruct ph; cbn [ph_slot atexit_ph] in ATX, PH; [destruct PH as (PF1 & PA1 & PFL)| clear PH].
-
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x658f08, 0x658f0c); (0x658ce8, 0x658d00); (0x102450, 0x102451);
(0x102400, 0x102408); (0x103370, 0x103378); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
(ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
unfold atexit_cells in ATX.
carve_frame 16%nat ST.
do 6 lstep.
rewrite (sx32_small_A tid ltac:(lia)).
lstep. lstep.

amo_step. showpc. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
astep. showpc. amo_step. showpc. astep. showpc.
astep. showpc. fold_sx32. fold_closed_in_goal.
astep. showpc. astep. showpc.
astep. showpc.

astep.
call funcs_on_exit_spec1; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| exact (conj PF1 (conj PA1 PFL))| assumption| lia| lia|].
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0x100ab0 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
| exact GDS1| exact ODRS| assumption|].
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
astep.
unfold exit_prefix_post. sys_finish.
-
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x658f08, 0x658f0c); (0x658ce8, 0x658d00); (0x102450, 0x102451);
(0x102400, 0x102408); (0x103370, 0x103378); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
(ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
unfold atexit_cells in ATX.
carve_frame 16%nat ST.
do 6 lstep.
rewrite (sx32_small_A tid ltac:(lia)).
lstep. lstep.
amo_step. showpc. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
astep. showpc. amo_step. showpc. astep. showpc.
astep. showpc. fold_sx32. fold_closed_in_goal.
astep. showpc. astep. showpc.
astep. showpc.
astep.
call funcs_on_exit_spec0; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| assumption| lia| lia|].
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0x100ab0 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
| exact GDS1| exact ODRS| assumption|].
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

astep.
unfold exit_prefix_post. sys_finish.
Qed.

Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : mem),
0 <= code < 2^64 -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (ra' : word),
ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
(Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6bb8) (Z_to_bv 64 94) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 0xe6e4c) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6e4c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros HC MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
do 4 lstep. step_ecall.
eexists. reflexivity.
Qed.

End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition exit_prefix_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo code : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR (Z_to_bv 64 0xde71c) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe4f38) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (0x6506c8, 0x6506cc); (0x6504a8, 0x6504c0); (0xf9c10, 0xf9c11);
(0xf9bc0, 0xf9bc8); (0xfab30, 0xfab38); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
(ODR_LO, ODR_HI)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma exit_prefix_spec : forall (ph : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word)
(flag dso : word),
a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 0x630458 -> 0 <= code < 2^64 ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> 0x800c0000 <= lo ->
rw_cells asegs m 0x6303b0 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
rw_cells asegs m 0x6504a8 (atexit_cells fin p1 p2 (ph_slot ph) 0x6504c0 0 0xde65c) ->
atexit_ph ph m ->
rw_cells asegs m 0x6505c8 [C8 (Z_to_bv 64 0x85c28)] ->
rw_cells asegs m 0x6506c8 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells asegs m 0x18f120 [C1 (Z_to_bv 8 0)] ->
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
evt asegs (exit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde6b0) fc None m (seg_rom asegs)).
Proof.
intros until dso. intros -> -> HC ST LO LOLO TID HT ATX PH ATA EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP
THR RMS SC1 SC2 SC3 GDS ODRS MI.
destruct ph; cbn [ph_slot atexit_ph] in ATX, PH; [destruct PH as (PF1 & PA1 & PFL)| clear PH].
-
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x6506c8, 0x6506cc); (0x6504a8, 0x6504c0); (0xf9c10, 0xf9c11);
(0xf9bc0, 0xf9bc8); (0xfab30, 0xfab38); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
(ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
unfold atexit_cells in ATX.
carve_frame 16%nat ST.
do 6 lstep.
rewrite (sx32_small_A tid ltac:(lia)).
lstep. lstep.

amo_step. showpc. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
astep. showpc. amo_step. showpc. astep. showpc.
astep. showpc. fold_sx32. fold_closed_in_goal.
astep. showpc. astep. showpc.
astep. showpc.

astep.
call funcs_on_exit_spec1; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| exact (conj PF1 (conj PA1 PFL))| assumption| lia| lia|].
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0xf8230 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
| exact GDS1| exact ODRS| assumption|].
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
astep.
unfold exit_prefix_post. sys_finish.
-
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x6506c8, 0x6506cc); (0x6504a8, 0x6504c0); (0xf9c10, 0xf9c11);
(0xf9bc0, 0xf9bc8); (0xfab30, 0xfab38); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
(ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
unfold atexit_cells in ATX.
carve_frame 16%nat ST.
do 6 lstep.
rewrite (sx32_small_A tid ltac:(lia)).
lstep. lstep.
amo_step. showpc. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
astep. showpc. amo_step. showpc. astep. showpc.
astep. showpc. fold_sx32. fold_closed_in_goal.
astep. showpc. astep. showpc.
astep. showpc.
astep.
call funcs_on_exit_spec0; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| assumption| lia| lia|].
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0xf8230 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
| exact GDS1| exact ODRS| assumption|].
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

astep.
unfold exit_prefix_post. sys_finish.
Qed.

Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : mem),
0 <= code < 2^64 -> mem_inv asegs m ->
evt asegs (fun ms' => exists (ra' : word),
ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
(Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde488) (Z_to_bv 64 94) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 0xde71c) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde71c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HC MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
do 4 lstep. step_ecall.
eexists. reflexivity.
Qed.


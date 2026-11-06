(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cr X1cs X1dg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05l X081 X082 X05m X09f X06d X069.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0ys X0yt X0x2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition USERH_DEPTH : Z := 64.
Definition STEREOH_DEPTH : Z := 96.
Definition INBAND_DEPTH : Z := 96.

Definition A_e_ratio_quant : Z := 0x23760.

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
Definition user_handler_bits b : bits_st ptr := speex_bits_advance (ub b 4) (5 + 8 * uv b 4).
Definition stereo_handler_bits b : bits_st ptr := ub (ub (ub b 1) 5) 2.
Definition inband_bits (stereo_cb : bool) b : bits_st ptr :=
let id := uv b 4 in let b1 := ub b 4 in
if stereo_cb && (id =? SPEEX_INBAND_STEREO) then stereo_handler_bits b1
else speex_bits_advance b1 (inband_skip_bits id).
End Pure.

Section Stmts.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition user_handler_postA (A D usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -USERH_DEPTH, usp)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ frm0 fc'
/\ bits_rep bsegs m' A D (user_handler_bits b) /\ bits_ok (user_handler_bits b).
Definition user_handler_stmtA : Prop :=
forall (A D ST usp lo : Z) b
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep bsegs m A D b -> bits_ok b ->
aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) ->
hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> IMG_TOP_B <= A ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
stk bsegs m lo usp -> lo <= usp - USERH_DEPTH -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (user_handler_postA A D usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 ST) (Z_to_bv 64 0) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_default_user_handler) fc None m (seg_rom bsegs)).

Definition stereo_handler_postA (A D STEREO usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (sws' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (STEREO, STEREO + 8); (usp + -STEREOH_DEPTH, usp)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ frm0 fc'
/\ rw_cells bsegs m' STEREO (f32 sws') /\ length sws' = 2%nat
/\ bits_rep bsegs m' A D (stereo_handler_bits b) /\ bits_ok (stereo_handler_bits b).

Definition inband_postA (sc : bool) (A D STEREO usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (sws' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (STEREO, STEREO + 8); (usp + -INBAND_DEPTH, usp)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ frm0 fc'
/\ rw_cells bsegs m' STEREO (f32 sws') /\ length sws' = 2%nat
/\ bits_rep bsegs m' A D (inband_bits sc b) /\ bits_ok (inband_bits sc b).
Definition inband_handler_stmtA : Prop :=
forall (sc : bool) (A D CBA ST STEREO usp lo : Z) b (js : list (list byte * list byte)) (sws : list word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep bsegs m A D b -> bits_ok b ->
rw_cells bsegs m CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js) ->
length js = 16%nat -> Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
rw_cells bsegs m STEREO (f32 sws) -> length sws = 2%nat ->
aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) -> aobj bsegs m CBA 640 -> aobj bsegs m STEREO 8 -> aobj bsegs m A_e_ratio_quant 16 ->
CBA mod 8 = 0 -> STEREO mod 4 = 0 ->
hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO) -> IMG_TOP_B <= A -> IMG_TOP_B <= STEREO ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> CBA + 640 <= lo -> STEREO + 8 <= lo ->
hidp (CBA + 640 <= A \/ A + BITS_SIZEOF <= CBA) -> hidp (CBA + 640 <= STEREO \/ STEREO + 8 <= CBA) ->
hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO) -> hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO) ->
stk bsegs m lo usp -> lo <= usp - INBAND_DEPTH -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> mem_inv bsegs m -> frm0 fc -> 0 < CBA ->
evt bsegs (inband_postA sc A D STEREO usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 CBA) (Z_to_bv 64 ST) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_inband_handler) fc None m (seg_rom bsegs)).
End Stmts.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition USERH_DEPTH : Z := 48.
Definition STEREOH_DEPTH : Z := 80.
Definition INBAND_DEPTH : Z := 80.

Definition A_e_ratio_quant : Z := 0x23720.

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
Definition user_handler_bits b : bits_st ptr := speex_bits_advance (ub b 4) (5 + 8 * uv b 4).
Definition stereo_handler_bits b : bits_st ptr := ub (ub (ub b 1) 5) 2.
Definition inband_bits (stereo_cb : bool) b : bits_st ptr :=
let id := uv b 4 in let b1 := ub b 4 in
if stereo_cb && (id =? SPEEX_INBAND_STEREO) then stereo_handler_bits b1
else speex_bits_advance b1 (inband_skip_bits id).
End Pure.

Section Stmts.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition user_handler_postA (A D usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -USERH_DEPTH, usp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ frm0 fc'
/\ bits_rep asegs m' A D (user_handler_bits b) /\ bits_ok (user_handler_bits b).
Definition user_handler_stmtA : Prop :=
forall (A D ST usp lo : Z) b
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep asegs m A D b -> bits_ok b ->
aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) ->
hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> IMG_TOP <= A ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
stk asegs m lo usp -> lo <= usp - USERH_DEPTH -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (user_handler_postA A D usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 ST) (Z_to_bv 64 0) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_default_user_handler) fc None m (seg_rom asegs)).

Definition stereo_handler_postA (A D STEREO usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (sws' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (STEREO, STEREO + 8); (usp + -STEREOH_DEPTH, usp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ frm0 fc'
/\ rw_cells asegs m' STEREO (f32 sws') /\ length sws' = 2%nat
/\ bits_rep asegs m' A D (stereo_handler_bits b) /\ bits_ok (stereo_handler_bits b).

Definition inband_postA (sc : bool) (A D STEREO usp lo : Z) b
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (sws' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (STEREO, STEREO + 8); (usp + -INBAND_DEPTH, usp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ frm0 fc'
/\ rw_cells asegs m' STEREO (f32 sws') /\ length sws' = 2%nat
/\ bits_rep asegs m' A D (inband_bits sc b) /\ bits_ok (inband_bits sc b).
Definition inband_handler_stmtA : Prop :=
forall (sc : bool) (A D CBA ST STEREO usp lo : Z) b (js : list (list byte * list byte)) (sws : list word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep asegs m A D b -> bits_ok b ->
rw_cells asegs m CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js) ->
length js = 16%nat -> Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
rw_cells asegs m STEREO (f32 sws) -> length sws = 2%nat ->
aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) -> aobj asegs m CBA 640 -> aobj asegs m STEREO 8 -> aobj asegs m A_e_ratio_quant 16 ->
CBA mod 8 = 0 -> STEREO mod 4 = 0 ->
hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO) -> IMG_TOP <= A -> IMG_TOP <= STEREO ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> CBA + 640 <= lo -> STEREO + 8 <= lo ->
hidp (CBA + 640 <= A \/ A + BITS_SIZEOF <= CBA) -> hidp (CBA + 640 <= STEREO \/ STEREO + 8 <= CBA) ->
hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO) -> hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO) ->
stk asegs m lo usp -> lo <= usp - INBAND_DEPTH -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (inband_postA sc A D STEREO usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 CBA) (Z_to_bv 64 ST) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_inband_handler) fc None m (seg_rom asegs)).
End Stmts.

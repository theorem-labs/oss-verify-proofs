(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cr X1cs X1dg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X082 X089 X0bn.
Import ListNotations.
Open Scope Z_scope.
Local Notation mem := (word -> option byte).

Section S.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Fixpoint scbb (n : nat) (have_sign shape_bits : Z) b : bits_st ptr :=
match n with
| O => b
| S n' => let b1 := if negb (have_sign =? 0) then ub b 1 else b in scbb n' have_sign shape_bits (ub b1 shape_bits)
end.

Definition scb_body_stmt : Prop :=
forall (INN PAR A D ssz nb scb sbits hs usp lo : Z) b (is0 : list word) (tb : list byte)
(c0 : word) (j8 j16 j24 j72 j80 jh1 jh2 : list byte) (r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),

ro_cells asegs m PAR (scb_par_cells ssz nb scb sbits hs) -> aobj asegs m PAR 24 -> PAR mod 8 = 0 -> 0x10000 <= PAR -> PAR + 24 <= IMG_TOP ->
1 <= ssz <= 20 -> In nb [2; 4; 5; 8] -> ssz * nb = 40 -> 1 <= sbits <= 8 -> 0 <= hs <= 1 ->
X1cg.u8ro asegs m scb tb -> Z.of_nat (length tb) = 2 ^ sbits * ssz -> aobj asegs m scb (2 ^ sbits * ssz) -> 0x10000 <= scb -> scb + 2 ^ sbits * ssz <= IMG_TOP ->

rw_cells asegs m (usp + -192) (scb_frame (C8 c0) (CB 8 j8) (CB 8 j16) (CB 8 j24) (C8 (Z_to_bv 64 (usp + -256))) (C8 (Z_to_bv 64 nb)) (C8 (Z_to_bv 64 (usp + -352)))
(C8 (Z_to_bv 64 A)) (C8 (Z_to_bv 64 (usp + -288))) (CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
rw_cells asegs m (usp + -288) [CB 96 jh1] -> rw_cells asegs m (usp + -384) [CB 96 jh2] ->
aobj asegs m (usp + -256) (4 * nb) -> aobj asegs m (usp + -352) (4 * nb) ->

bits_rep asegs m A D b -> bits_ok b -> aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) ->
(A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> IMG_TOP <= A ->

rw_cells asegs m INN (f32 is0) -> length is0 = 40%nat -> aobj asegs m INN 160 -> INN mod 4 = 0 -> IMG_TOP <= INN ->
(INN + 160 <= SH_LO \/ SH_HI <= INN) -> (INN + 160 <= lo \/ usp <= INN) -> (A + BITS_SIZEOF <= INN \/ INN + 160 <= A) -> (D + sb_buf_size b <= INN \/ INN + 160 <= D) ->
stk asegs m lo (usp + -384) -> lo <= usp - 4384 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' : word)
(c0' c8' c16' c24' c32' c40' c48' : word) (jh1' jh2' : list byte)
(F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (is' : list word),
ms' = MS (mkR ra' (Z_to_bv 64 (usp + -384)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' s4' s5' s6' s7' s8' (Z_to_bv 64 SHB) s10' s11' t3' t4' t5' t6')
F' (Z_to_bv 64 A_scb_epi) fc' None m' (seg_rom asegs)
/\ munch [(usp + -416, usp + -384); (usp + -384, usp + -192); (usp + -192, usp + -120); (INN, INN + 160); (A, A + BITS_SIZEOF)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ frm0 fc' /\ stk asegs m' lo (usp + -384)
/\ rw_cells asegs m' (usp + -192) (scb_frame (C8 c0') (C8 c8') (C8 c16') (C8 c24') (C8 c32') (C8 c40') (C8 c48') (C8 (Z_to_bv 64 A)) (C8 (Z_to_bv 64 (usp + -384)))
(CB 8 j72) (CB 8 j80) r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)
/\ rw_cells asegs m' (usp + -288) [CB 96 jh1'] /\ rw_cells asegs m' (usp + -384) [CB 96 jh2']
/\ bits_rep asegs m' A D (scbb (Z.to_nat nb) hs sbits b) /\ bits_ok (scbb (Z.to_nat nb) hs sbits b)
/\ rw_cells asegs m' INN (f32 is') /\ length is' = 40%nat)
(MS (mkR (Z_to_bv 64 RA_scb_pois2) (Z_to_bv 64 (usp + -384)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 INN) (Z_to_bv 64 nb) (Z_to_bv 64 (usp + -384)) (Z_to_bv 64 (usp + -288)) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) (Z_to_bv 64 ssz) (Z_to_bv 64 SHB)
(Z_to_bv 64 ssz) (Z_to_bv 64 scb) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_scb_pois2)) fc None m (seg_rom asegs)).
End S.

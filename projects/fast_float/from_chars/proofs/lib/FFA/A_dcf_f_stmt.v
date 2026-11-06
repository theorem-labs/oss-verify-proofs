(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_rt_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_long_mul_stmt A_parse_mantissa_stmt A_negative_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_negative_digit_comp_d_stmt.A_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_parse_mantissa_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_negative_digit_comp_d_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.
Notation DCFF_ENTRY := 0x9b018%Z.
Notation DCFF_EXIT := 0x9b078%Z.

(* [comment removed for export] *)
Definition dcf_f_W (sp A FS pos0 : Z) : list ivl :=
  [(sp - NDC_NEED, sp); (A, A + 504); (sp + 80, sp + 88);
   (FS + 32, FS + 48);
   (FS + FK4_FLAGS, FS + FK4_FLAGS + pos0); (FS + FK4_FLAGS + pos0 + 1, FS + FK5_FLAGS + FK5_NFLAGS);
   (FS + FK4_LO, FS + FK4_LO + pos0 * 1024); (FS + FK4_LO + pos0 * 1024 + 1024, FS + FK5_HI);
   (ASAN_B + FS / 8 + FK4_SLO, ASAN_B + FS / 8 + FK4_SLO + pos0 * 128);
   (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128, ASAN_B + FS / 8 + FK5_SHI)]%Z.

Definition dcf_f_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (v : rt_vals) (pos0 : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (h4' h5' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 DCFF_EXIT) fc None m' (seg_rom ASEGS)
    /\ munch (dcf_f_W (bv_unsigned sp) A (rt_FS v) pos0) m m'
    /\ wmono ASEGS m m'
    /\ stk ASEGS m' (bv_unsigned sp - NDC_NEED) (bv_unsigned sp) /\ stk ASEGS m' (bv_unsigned sp + 80) (bv_unsigned sp + 88)
    /\ stk ASEGS m' A (A + 504)
    /\ pristine m' IMG_LO ROD_HI
    /\ RT m' v
    /\ fk4_nest m' (rt_FS v) h4' pos0
    /\ fk5_inv m' (rt_FS v) h5'.

Definition dcf_f_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (h4 h5 : word) (pos0 : Z) (old : list byte)
         (iptr fptr : word) (ibs fbs : list byte) (dg : word) (TLO THI gi gin gf gfn se p2 : Z),
    let FS := rt_FS v in
    let A := bv_unsigned s9 in
    let SP := bv_unsigned sp in
    let NP := bv_unsigned s5 in
    (* [comment removed for export] *)
    tp = Z_to_bv 64 TPV -> s1 = sp ->
    s10 = Z_to_bv 64 se -> (-342 <= se <= 358)%Z ->
    (bv_unsigned s7 mod 2 ^ 32 = (p2 - 32768) mod 2 ^ 32)%Z -> (- 2 ^ 14 <= p2 <= 2 ^ 14)%Z ->
    (* [comment removed for export] *)
    stk ASEGS m (SP - NDC_NEED) SP -> (SP mod 16 = 0)%Z ->
    (IMG_END <= SP - NDC_NEED)%Z -> (KHI <= SP - NDC_NEED)%Z -> (SP + 88 <= KTOP)%Z ->
    shz ASEGS m (ASAN_B + (SP - 2672) / 8) 334 ->
    rw_cells ASEGS m (SP + 80) [C8 dg] -> shz ASEGS m (ASAN_B + (SP + 80) / 8) 1 ->
    (* [comment removed for export] *)
    u8arr ASEGS m A old -> length old = 504%nat -> (A mod 8 = 0)%Z ->
    (FS + FK4_LO + pos0 * 1024 + 32 <= A)%Z -> (A <= FS + FK4_LO + pos0 * 1024 + 32)%Z ->   (* [comment removed for export] *)
    (A + 512 <= SP - NDC_NEED)%Z ->
    shz ASEGS m (ASAN_B + A / 8) 63 -> rdbl ASEGS m (ASAN_B + A / 8 - 8) 79 ->
    (* [comment removed for export] *)
    rw_cells ASEGS m (NP + 32)
        [C8 iptr; C8 (Z_to_bv 64 (Z.of_nat (length ibs))); C8 fptr; C8 (Z_to_bv 64 (Z.of_nat (length fbs)))] ->
    (NP mod 8 = 0)%Z -> (A + 504 <= NP + 32)%Z -> (NP + 64 <= FS + FSSIZE)%Z ->
    shz ASEGS m (ASAN_B + (NP + 32) / 8) 4 ->
    bytes_at ASEGS m (bv_unsigned iptr) ibs -> (bv_unsigned iptr <> 0)%Z ->
    (bv_unsigned iptr + Z.of_nat (length ibs) < 2^64)%Z -> (Z.of_nat (length ibs) < 2^40)%Z ->
    bytes_at ASEGS m (bv_unsigned fptr) fbs ->
    (bv_unsigned fptr + Z.of_nat (length fbs) < 2^64)%Z -> (Z.of_nat (length fbs) < 2^40)%Z ->
    (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z ->
    (app2r (TLO) (THI))%Z -> (TLO <= bv_unsigned iptr)%Z -> (bv_unsigned iptr + Z.of_nat (length ibs) <= THI)%Z ->
    (bv_unsigned fptr <> 0 -> TLO <= bv_unsigned fptr /\ bv_unsigned fptr + Z.of_nat (length fbs) <= THI)%Z ->
    (THI <= A \/ A + 504 <= TLO)%Z -> (THI <= SP - NDC_NEED)%Z ->
    shz ASEGS m (ASAN_B + gi) gin -> (0 <= gi <= bv_unsigned iptr / 8)%Z ->
    (bv_unsigned iptr + Z.of_nat (length ibs) <= 8 * (gi + gin) <= KTOP)%Z ->
    (bv_unsigned fptr <> 0 ->
       shz ASEGS m (ASAN_B + gf) gfn /\ 0 <= gf <= bv_unsigned fptr / 8 /\
       bv_unsigned fptr + Z.of_nat (length fbs) <= 8 * (gf + gfn) <= KTOP)%Z ->
    (* [comment removed for export] *)
    pristine m IMG_LO ROD_HI -> pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (SP - NDC_NEED) (SP + 88) -> rt_disj v A (A + 504) -> rt_disj v FS (FS + FSSIZE) ->
    shz ASEGS m TBL10_SH TBL10_SHN -> shz ASEGS m POW5TAB_SH POW5TAB_SHN ->
    rdbl ASEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
    fk4_nest m FS h4 pos0 -> (0 <= pos0 < 1024)%Z -> (bv_unsigned h4 mod 1024 <> pos0)%Z ->
    fk5_inv m FS h5 ->
    (FS + FSSIZE <= SP - NDC_NEED)%Z ->
    RTX v fc ->   (* [comment removed for export] *)
    evt ASEGS (dcf_f_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A v pos0 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DCFF_ENTRY) fc None m (seg_rom ASEGS)).

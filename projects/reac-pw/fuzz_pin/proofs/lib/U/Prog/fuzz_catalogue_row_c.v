From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
Import ListNotations.
Open Scope Z_scope.

(** fuzz_catalogue_row (catalogue.c:29-35; 136 bytes, 34 instructions at 0x130ac in the UBSan image; frame 48 bytes,
    saves ra, s0-s4). The plain code with the UBSan addresses (elfdis level 3 identical; no UBSan check in it): the
    table FUZZ_CATALOGUE = 0x1c848 (0x130d4 `auipc a0,9; addi s0,a0,0x774`), strlen at 0x1b334 (0x130e4), bcmp at
    0x1ab40 (0x130f8). Everything else as lib/Prog/fuzz_catalogue_row_c.v: it returns row_ptr FUZZ_CATALOGUE sb,
    reads the table (rw- segment [0x1c000, 0x1e000): the table premise), the tokens (.rodata: mem_inv) and the n bytes
    at s, writes only [sp - 48, sp).

    Callee contracts its walk takes as premises: U/Prog/strlen_c.v strlen_contract (STRLEN = 0x1b334) and
    U/Prog/bcmp_c.v bcmp_contract (BCMP = 0x1ab40) (the released forms relocated to pin's UBSan image).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x12e68 `jal fuzz_catalogue_row`, reached only when strlen(spec) <> 0
    and flags & 7 = 0 (0x12dac), with a0 = s0 = spec (0x12e60), a1 = s2 = tok (0x12e64), sp = S - 80. Why each
    premise holds there: as in the plain build. *)
Definition FUZZ_CATALOGUE_ROW : Z := 0x130ac.
Definition FUZZ_CATALOGUE : Z := 0x1c848.
Definition FCR_STACK : Z := 48.

Definition fuzz_catalogue_row_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sb : list byte) (lo : Z),
    bytes_at rsegs m (bv_unsigned a0) sb ->
    bv_unsigned a1 = Z.of_nat (length sb) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + FCR_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    (bv_unsigned a0 + Z.of_nat (length sb) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (row_ptr FUZZ_CATALOGUE sb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - FCR_STACK, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_CATALOGUE_ROW) fc None m (seg_rom rsegs)).

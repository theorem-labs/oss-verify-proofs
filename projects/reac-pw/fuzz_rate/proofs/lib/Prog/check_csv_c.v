From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** check_csv(buf, buflen, len, mask) (fuzz_rate.c:217-229, csv_holds :103-128 inlined; 336 bytes, 84 instructions at
    0x14734 in the plain image; frame 96 bytes: ra, s0-s4 at sp + 0x30 .. sp + 0x5f, d[8] at sp .. sp + 7,
    want[40] at sp + 8 .. sp + 0x2f):
      0x14734 .. 0x14784 saves; s0 = buf, s1 = len; a0 = i = 0; a7 = n = 0; t1 = 0x10648 (closed_list, .rodata);
      0x14788 .. 0x1481c the loop over i = 0, 1, 2 (`bne a0,a4` with a4 = 3): `srlw t4,a3,a0; andi t4,t4,1` (bit i
              of mask), `beqz` skips; `lw t6` = closed_list[i]; the do-while digit loop 0x147a8-0x147dc (v / 10 by
              `mul 0x66666667; srai 34`) writes d[]; `,` at want[n] when n > 0; the reverse copy 0x14804-0x14814;
      0x14820 `bne s1,a7` (len != n) -> abort; `beqz a1` (buflen = 0) -> 0x14874: `lbu a0,0(s0)`, `beq a0,0x5a`
              returns, else abort; else c = min(len, buflen - 1) (unsigned), bcmp(buf, want, c) (0x14840 ->
              0x1cdf8, a tail jump to memcmp 0x1cdfc), `bnez` -> abort, `lbu buf[c]`, `bnez` -> abort; restores, ret;
      0x14880 jal abort (0x160bc).
    want is csv_list (bv_unsigned a3) (Pod/RateCsv.v: the digit loop writes the decimal digits of each closed rate,
    csv_dec, which RateCsv.csv_dec_rates gives as constants; n <= 17 < 40). So with len = |want|, and buf holding
    0x5a (buflen = 0) or csv_cut want buflen and a NUL (buflen > 0), no branch to abort is taken: bcmp compares
    the first c bytes of buf with the first c bytes of want, equal by csv_cut's definition, and buf[c] = 0. On that
    path it writes the caller-saved integer registers (bcmp/memcmp too) and its frame, restores ra and s0-s4, and
    reads closed_list (in the read-only segment at 0x10000: mem_inv makes those reads come from the image), buf and
    want; buf lies outside its frame, so the frame stores leave buf's bytes as they were.

    Callee contract its walk takes as a premise: bcmp_contract (Prog/bcmp_c.v, BCMP = 0x1cdf8; disco's, copied),
    with ls = rs = csv_bytes (csv_cut want buflen) and memcmp_model ls ls c = Some 0 (released ctrl
    Prog/Seg/G03.v:24 g03_memcmp).

    Call site (LLVMFuzzerTestOneInput, plain): 0x14548 `jal check_csv`, with sp = S0 - 544 (the harness frame) and
      a0 = s4 = buf (0x1453c `mv a0,s4`), a1 = s10 = buflen (0x14540), a2 = reac_rate_drivable_csv's result
      (0x14538 `mv a2,a0`), a3 = s9 = mask (0x14544).
    Why each premise holds there: reac_rate_drivable_csv_contract returns a0' = |csv_list mask| and, for buflen > 0,
    bytes_at buf (csv_bytes (csv_cut L buflen ++ [0])); for buflen = 0 it leaves memory outside the stack region
    as it was (munch [(lo, S)]), so buf[0] still holds main's memset 0x5a (memset(buf, 0x5a, 1) at 0x14524;
    the heap block lies below lo). buflen <= 23; s4, s9, s10 are callee-saved across drivable_csv. The stack region
    [lo, sp) is the frame's stack, writable, outside the image, lo + 96 <= S0 - 544; mem_inv holds after
    drivable_csv (its post). *)
Definition CHECK_CSV : Z := 0x14734.
Definition CHECK_CSV_FRAME : Z := 96.

Definition check_csv_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    let S := bv_unsigned sp in let buf := bv_unsigned a0 in let n := bv_unsigned a1 in
    let L := csv_list (bv_unsigned a3) in
    bv_unsigned a2 = Z.of_nat (length L) ->
    n <= 23 ->
    (n = 0 -> bytes_at rsegs m buf [Z_to_bv 8 0x5a]) ->
    (0 < n -> bytes_at rsegs m buf (csv_bytes (csv_cut L n ++ [0]))) ->
    (buf + Z.max n 1 <= lo \/ S <= buf) ->
    stk rsegs m lo S -> lo + CHECK_CSV_FRAME <= S ->
    (forall a, lo <= a < S -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(S - CHECK_CSV_FRAME, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CSV) fc None m (seg_rom rsegs)).

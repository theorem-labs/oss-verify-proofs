From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** check_csv(buf, buflen, len, mask) (fuzz_rate.c:217-229, csv_holds :103-128 inlined; 436 bytes, 109 instructions at
    0x14864 in the UBSan image; frame 144 bytes: ra, s0-s9 at sp + 0x38 .. sp + 0x8f, d[8] at sp + 8 .. sp + 0xf,
    want[40] at sp + 0x10 .. sp + 0x37):
      0x14864 .. 0x148d4 saves; s0 = buf, s1 = len; a0 = i = 0; t6 = n = 0; t3 = 0x10628 (closed_list, .rodata);
      0x148d8 .. 0x14990 the loop over i = 0, 1, 2 (`bne a0,a2` with a2 = 3): `srlw s2,a3,a0; andi s2,s2,1`, `beqz`
              skips; `lw s5` = closed_list[i]; the digit loop 0x148f8-0x14938 writes d[] (trap test 0x148f8
              `beq s2,a4` with a4 = 8: k = 8); `,` at want[n] when n > 0 (trap test 0x14940 `bltu t2,t6`, n > 39); the
              reverse copy 0x14958-0x14984 (trap tests 0x14964 `bltu a4,s2`, k > 8, and 0x14968 `beq t6,t1`, n = 40);
      0x14994 `bne s1,t6` (len != n) -> abort; `beqz a1` (buflen = 0) -> 0x14a04: `lbu a0,0(s0)`, `beq a0,0x5a`
              returns, else abort; else c = min(len, buflen - 1), bcmp(buf, want, c) (0x149b4 -> 0x1d1e0, a tail jump
              to memcmp 0x1d1e4), `bnez` -> abort, trap test 0x149c0 `bltu ~buf,c` (buf + c wraps), `lbu buf[c]`,
              `bnez` -> abort; restores, ret;
      0x14a10 jal abort (0x164a4); 0x14a14 unimp (the trap target and the slot after abort).
    The five trap branches are never taken: k <= 5 digits, n <= 17, and buf + c < 2^64 (bytes_at's bound). want is
    csv_list (bv_unsigned a3) (Pod/RateCsv.v), so with len = |want| and buf holding 0x5a (buflen = 0) or csv_cut want
    buflen and a NUL (buflen > 0), no branch to abort is taken. On that path it writes the caller-saved integer
    registers (bcmp/memcmp too) and its frame, restores ra and s0-s9, and reads closed_list (in the read-only segment
    at 0x10000: mem_inv makes those reads come from the image), buf and want; buf lies outside its frame.

    Callee contract its walk takes as a premise: bcmp_contract (U/Prog/bcmp_c.v, BCMP = 0x1d1e0; disco's, copied),
    with ls = rs = csv_bytes (csv_cut want buflen) and memcmp_model ls ls c = Some 0.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x1465c `jal check_csv`, with sp = S0 - 592 (the harness frame) and
      a0 = s4 = buf (0x14650 `mv a0,s4`), a1 = s0 = buflen (0x14654), a2 = reac_rate_drivable_csv's result
      (0x1464c `mv a2,a0`), a3 = s10 = mask (0x14658).
    Why each premise holds there: as in the plain image (Prog/check_csv_c.v): drivable_csv's post and main's memset
    0x5a (0x14638); s0, s4, s10 are callee-saved across drivable_csv; lo + 144 <= S0 - 592. *)
Definition CHECK_CSV : Z := 0x14864.
Definition CHECK_CSV_FRAME : Z := 144.

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

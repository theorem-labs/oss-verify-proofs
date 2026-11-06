From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_cells_valid(out, rc) (fuzz_headamp.c:207-219 with cells_valid :161-169 inlined; 112 bytes, 28 instructions
    at 0x1491c in the UBSan image; no frame on the path that returns):
      0x1491c blez a1,0x14978; mv a2,zero; not a3,a0; slli a6,a1,1; addi a4,a0,2; addi a5,zero,0x2f;
              add a1,a6,a1; addi a6,zero,2;
      0x1493c bltu a3,a2,0x14988; add a7,a0,a2; lbu t0,0(a7); bltu a5,t0,0x1497c; lbu a7,1(a7);
              bltu a6,a7,0x1497c; beq a7,a6,0x14960; addi a7,zero,1; j 0x14964; 0x14960 addi a7,zero,0x37;
      0x14964 add t0,a4,a2; lbu t0,0(t0); bltu a7,t0,0x1497c; addi a2,a2,3; bne a1,a2,0x1493c;
      0x14978 ret;
      0x1497c addi sp,sp,-16; sd ra,8(sp); jal abort (0x16364); 0x14988 unimp.
    The loop walks the byte offset a2 = 3i up to 3 rc; the UBSan check at its head, ~out <u 3i (the pointer
    overflow of out + 3i) goes to the trap 0x14988, and is false when out + 3 rc <= 2^64 (bytes_at's bound). The
    tests are the plain build's (lib/Prog/check_cells_valid_c.v): it returns exactly when rc <= 0 or every one of
    the rc cells at out is valid. On that path it writes a1-a7 and t0 (only when rc > 0), keeps a0, stores nothing
    and uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14188 `jal check_cells_valid` (the only one), with sp = S - 608 and
      a0 = s3 = out (0x14180), a1 = s6 = rc (0x14184; 0x14164 `mv s6,a0` after the parse at 0x14158).
    Why the premises hold there: the parse contract stores ha_cells_bytes cells at out; parse_props_total gives
    rc = |cells| for rc >= 0 and every cell valid: U/Prog/HeadSites.v [site_cells_valid]. *)
Definition CHECK_CELLS_VALID : Z := 0x1491c.

Definition check_cells_valid_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rc : Z) (cs : list cell),
    a1 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 ->
    (0 < rc ->
       bytes_at rsegs m (bv_unsigned a0) (ha_cells_bytes cs) /\ Z.of_nat (length cs) = rc /\
       Forall cell_valid cs) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CELLS_VALID) fc None m (seg_rom rsegs)).

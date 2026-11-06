From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_keys(res, x) (fuzz_headamp.c:261-271; 28 bytes, 7 instructions at 0x147e0 in the plain image):
      0x147e0 lw a0,4(a0); lw a1,0x80(a1); bne a0,a1,0x147f0; ret;
      0x147f0 addi sp,sp,-16; sd ra,8(sp); jal abort (0x15e64).
    It returns exactly when res->keys (at res + 4) and x->keys (at x + 0x80) are the same int, the C condition of :269
    false: the premises state it as the same four bytes w at both places (lw reads exactly those four bytes,
    sign-extended). On that path it writes a0, a1, stores nothing and uses no stack.

    Call site (LLVMFuzzerTestOneInput, plain): 0x14138 `jal check_keys` (the only one), reached when pp->corrupt = 0
    and rc >= 0 (0x1412c `bltz s6` not taken), just after check_cells returned, with sp = S - 560 and
      a0 = sp + 0x150 = &res (0x14130), a1 = sp + 0x90 = &x (0x14134).
    Why the premises hold there: the parse contract stored ans_res_bytes (parse_props props cap) at res and M03's walk
    shows x = x_bytes (expect_model null cap r) (Spec/HeadBytes.v: keys at X_KEYS_OFF = 0x80); parse_props props cap =
    expect_model null cap r (parse_props_build), so w = le4 (Z_to_bv 64 keys) at both: Prog/HeadSites.v
    [site_keys]. *)
Definition CHECK_KEYS : Z := 0x147e0.

Definition check_keys_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w : list byte),
    length w = 4%nat ->
    bytes_at rsegs m (bv_unsigned a0 + 4) w -> bytes_at rsegs m (bv_unsigned a1 + X_KEYS_OFF) w ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_KEYS) fc None m (seg_rom rsegs)).

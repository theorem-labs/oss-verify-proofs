From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_count(rc, cap, res) (fuzz_headamp.c:194-205; 48 bytes, 12 instructions at 0x146b0 in the plain image):
      0x146b0 addi a3,zero,-1; blt a0,a3,0x146d4; blt a1,a0,0x146d4; bltz a0,0x146d0;
              lw a1,0(a2); bne a1,a0,0x146d4; lw a1,4(a2); blt a1,a0,0x146d4;
      0x146d0 ret;
      0x146d4 addi sp,sp,-16; sd ra,8(sp); jal abort (0x15e64).
    The compares are signed 64-bit on the int arguments (sign-extended in a0, a1) and on res->n, res->keys (lw
    sign-extends). It returns exactly when the C condition of :203 is false: -1 <= rc <= cap, and for rc >= 0,
    res->n = rc and res->keys >= rc. The premises state that on the eight bytes it reads at a2 (the n and keys words
    of struct reac_headamp_prop_result: n = rc, keys in [rc, 2^31)); for rc = -1 it reads no memory. On that path it
    writes a3 := -1 and, when rc >= 0, a1 (the two lw), stores nothing and uses no stack (only the abort path has a
    frame; the premises make it dead).

    Call site (LLVMFuzzerTestOneInput, plain): 0x140d8 `jal check_count` (the only one), on every run past the first
    three mallocs, with sp = S - 560 and
      a0 = s6 = rc (0x140d0 `mv a0,s6`; 0x140c0 `mv s6,a0` after reac_headamp_prop_parse_result at 0x140bc);
      a1 = s2 = cap (0x140d4; 0x14054 `andi s2,s6,0xff`, the second input byte mod 10);
      a2 = sp + 0x150 = &res (0x140cc), the 12 bytes the parse was given as its a3 (0x140ac).
    Why the premises hold there: the parse contract (Prog/reac_headamp_prop_parse_result_c.v) returns
    a0 = Z_to_bv 64 rc and stores ha_res_bytes n keys refusal at res, for (rc, cells, (n, keys, refusal)) =
    parse_props props cap; Pod/Headamp.v's parse_props_total (answer_ok: rc = -1, or 0 <= rc <= cap with n = rc and
    rc <= keys) and parse_props_keys (keys <= the pod's length <= 16384 < 2^31) give the premises, with cap <= 9:
    Prog/HeadSites.v [site_count]. *)
Definition CHECK_COUNT : Z := 0x146b0.

Definition check_count_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rc cap keys : Z),
    a0 = Z_to_bv 64 rc -> a1 = Z_to_bv 64 cap -> -1 <= rc <= cap -> cap < 2 ^ 31 ->
    (0 <= rc ->
       bytes_at rsegs m (bv_unsigned a2) (le4 (Z_to_bv 64 rc) ++ le4 (Z_to_bv 64 keys)) /\ rc <= keys < 2 ^ 31) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 (Z_to_bv 64 (-1)) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_COUNT) fc None m (seg_rom rsegs)).

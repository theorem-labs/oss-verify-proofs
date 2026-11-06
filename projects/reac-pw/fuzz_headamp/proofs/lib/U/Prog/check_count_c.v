From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_count(rc, cap, res) (fuzz_headamp.c:194-205; 60 bytes, 15 instructions at 0x148e0 in the UBSan image):
      0x148e0 addi a3,zero,-1; blt a0,a3,0x1490c; blt a1,a0,0x1490c; bltz a0,0x14908;
              andi a1,a2,3; bnez a1,0x14918; lw a1,0(a2); bne a1,a0,0x1490c; lw a1,4(a2); blt a1,a0,0x1490c;
      0x14908 ret;
      0x1490c addi sp,sp,-16; sd ra,8(sp); jal abort (0x16364); 0x14918 unimp.
    The plain text (lib/Prog/check_count_c.v) with one UBSan check before the loads: res & 3 <> 0 (the alignment of
    the struct reac_headamp_prop_result access) goes to the trap 0x14918, discharged by the premise res mod 4 = 0
    for rc >= 0 (for rc = -1 the test is not reached). On the path that returns it writes a3 := -1 and, when
    rc >= 0, a1 (the andi, then the two lw), stores nothing and uses no stack.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x1417c `jal check_count` (the only one), with sp = S - 608 and
      a0 = s6 = rc (0x14174; 0x14164 `mv s6,a0` after reac_headamp_prop_parse_result at 0x14158);
      a1 = s2 = cap (0x14178; 0x140ec `lbu s2,8(sp)`, cap = the second input byte mod 10);
      a2 = sp + 0x178 = &res (0x14170), the parse's a3 (0x14148).
    Why the premises hold there: as in the plain file (parse_props_total, parse_props_keys, cap <= 9), and
    res = S - 608 + 0x178 is 4-aligned (S mod 16 = 0, GV): U/Prog/HeadSites.v [site_count]. *)
Definition CHECK_COUNT : Z := 0x148e0.

Definition check_count_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rc cap keys : Z),
    a0 = Z_to_bv 64 rc -> a1 = Z_to_bv 64 cap -> -1 <= rc <= cap -> cap < 2 ^ 31 ->
    (0 <= rc ->
       bv_unsigned a2 mod 4 = 0 /\
       bytes_at rsegs m (bv_unsigned a2) (le4 (Z_to_bv 64 rc) ++ le4 (Z_to_bv 64 keys)) /\ rc <= keys < 2 ^ 31) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 (Z_to_bv 64 (-1)) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_COUNT) fc None m (seg_rom rsegs)).

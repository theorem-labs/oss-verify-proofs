From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import reac_rate_refuse_code_c.
Import ListNotations.
Open Scope Z_scope.

(** check_code(got, r) (fuzz_rate.c:190-200, code_of :52-61 inlined; 80 bytes, 20 instructions at 0x1461c in the plain
    image; frame 16 bytes, saves ra at sp - 8):
      0x1461c addi sp,sp,-16; sd ra,8(sp); addiw a1,a1,-1; addi a2,zero,3; bltu a2,a1,0x1464c;
              slli a1,a1,2; auipc a2,0xffffc; addi a2,a2,0x20 (a2 = 0x14634 - 0x4000 + 0x20 = 0x10654 = CODE_TBL);
              add a1,a2,a1; lw a1,0(a1); add a1,a2,a1; j 0x14654;
      0x1464c auipc a1,0xffffc; addi a1,a1,-0x26b (a1 = 0x1464c - 0x4000 - 0x26b = 0x103e1, "none");
      0x14654 jal strcmp (0x1d328); bnez a0,0x14668; ld ra,8(sp); addi sp,sp,16; ret;
      0x14668 jal abort (0x160bc).
    code_of became a relative table of four 32-bit offsets at CODE_TBL = 0x10654 (.rodata) for r - 1 in [0, 3]
    (`addiw` makes r - 1 a sign-extended 32-bit value; the unsigned `bltu` sends every other value, r = 0 included,
    to "none"). Its targets are the very strings reac_rate_refuse_code's table points to (the strings are merged):
    code_of_addr r = refuse_code_addr r for 0 <= r <= 4 ([code_of_addr_refuse]; [code_tbl_img] reads the table).
    So with a0 = refuse_code_addr r and 0 <= r <= 4 the strcmp compares one string with itself, refuse_code_res r
    (whose image bytes [refuse_code_addr_img] gives, no NUL inside, Pod/RateCfg.v refuse_code_res_nonul), and
    strcmp_contract's r = 0 <-> sx = sy gives 0: the bnez is not taken. The premise r <= 4 is needed: the 32-bit
    `addiw` and refuse_code's 64-bit `bgeu` disagree when a1 has high bits set (a1 = 2^32 + 1: refuse_code answers
    "none", code_of indexes entry 0, "not_closed"). On that path it writes a0-a3 (strcmp writes a0-a3; a1, a2 also
    here), stores ra in its frame [sp - 16, sp) and loads it back, and reads the table entry and the string (both in
    .rodata, in the read-only segment at 0x10000: mem_inv makes those reads come from the image; the stack premise
    keeps the frame store off them).

    Callee contract its walk takes as a premise: strcmp_contract (Prog/strcmp_c.v, STRCMP = 0x1d328; role's,
    relocated), with sx = sy = refuse_code_res r read from the image.

    Call sites (LLVMFuzzerTestOneInput, plain), with sp = S - 544 (the harness frame):
      0x144a8 `jal check_code` in the two-pass decide loop, with a0 = reac_rate_refuse_code(r) (the call at 0x144a0
              with a0 = s6) and a1 = s6 = r (0x144a4 `mv a1,s6`), r = reac_rate_cfg_decide's result (0x14424);
      0x14500 `jal check_code` after the loop, with a0 = reac_rate_refuse_code(4) (the call at 0x144f8) and a1 = 4
              (0x144fc `addi a1,zero,4`).
    Why each premise holds there: reac_rate_cfg_decide_contract gives r = Z_to_bv 64 (decide_res ...) with
    0 <= decide_res <= 3 (Pod/RateCfg.v decide_res_range), and 4 is 4; reac_rate_refuse_code_contract gives
    a0 = Z_to_bv 64 (refuse_code_addr (bv_unsigned r)). The stack region [lo, sp) with lo = S - 65536 is the frame's
    stack (stk), writable and outside the image (seg_rom None), and lo + 16 <= S - 544; mem_inv holds of the memory
    the cut runs on and every callee since keeps it. *)
Definition CHECK_CODE : Z := 0x1461c.
Definition CHECK_CODE_FRAME : Z := 16.
Definition CODE_TBL : Z := 0x10654.

(** code_of(r) as the address the code compares with. *)
Definition code_of_addr (r : Z) : Z :=
  if r =? 1 then CODE_NOT_CLOSED else if r =? 2 then CODE_NOT_DRIVABLE else if r =? 3 then CODE_ROLE_SLAVE
  else if r =? 4 then CODE_MALFORMED else CODE_NONE.

Lemma code_of_addr_refuse : forall r, 0 <= r <= 4 -> code_of_addr r = refuse_code_addr r.
Proof.
  intros r Hr. assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) as H by lia.
  destruct H as [->|[->|[->|[->| ->]]]]; reflexivity.
Qed.

(** code_of's table: entry i (r = i + 1) is code_of_addr (i + 1) - CODE_TBL, as a 32-bit word. *)
Lemma code_tbl_img : forall i, (i < 4)%nat ->
  option_map le_val (img_bytes (CODE_TBL + 4 * Z.of_nat i) 4) = Some ((code_of_addr (Z.of_nat i + 1) - CODE_TBL) mod 2^32).
Proof.
  intros i Hi. destruct i as [|[|[|[|i]]]]; [ | | | | exfalso; lia]; vm_compute; reflexivity.
Qed.

Definition check_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a1 <= 4 ->
    a0 = Z_to_bv 64 (refuse_code_addr (bv_unsigned a1)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_CODE_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CODE_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CODE) fc None m (seg_rom rsegs)).

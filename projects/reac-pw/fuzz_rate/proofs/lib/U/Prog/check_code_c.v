From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import reac_rate_refuse_code_c.
Import ListNotations.
Open Scope Z_scope.

(** check_code(got, r) (fuzz_rate.c:190-200, code_of :52-61 inlined; 84 bytes, 21 instructions at 0x14744 in the UBSan
    image; frame 16 bytes, saves ra at sp - 8):
      0x14744 addi sp,sp,-16; sd ra,8(sp); addiw a1,a1,-1; addi a2,zero,3; bltu a2,a1,0x14774;
              slli a1,a1,2; auipc a2,0xffffc; addi a2,a2,-0x128 (a2 = 0x1475c - 0x4000 - 0x128 = 0x10634 = CODE_TBL);
              add a1,a2,a1; lw a1,0(a1); add a1,a2,a1; j 0x1477c;
      0x14774 auipc a1,0xffffc; addi a1,a1,-0x393 (a1 = 0x14774 - 0x4000 - 0x393 = 0x103e1, "none");
      0x1477c jal strcmp (0x1d710); bnez a0,0x14790; ld ra,8(sp); addi sp,sp,16; ret;
      0x14790 jal abort (0x164a4); 0x14794 unimp (after abort, never reached).
    The plain code (Prog/check_code_c.v) at another address, plus the unimp; no trap branch. code_of is a relative
    table of four 32-bit offsets at CODE_TBL = 0x10634 (.rodata) for r - 1 in [0, 3]; its targets are the strings
    reac_rate_refuse_code's table points to: code_of_addr r = refuse_code_addr r for 0 <= r <= 4
    ([code_of_addr_refuse]; [code_tbl_img] reads the table). With a0 = refuse_code_addr r and 0 <= r <= 4 the strcmp
    compares one string with itself (refuse_code_res r, U/Prog/reac_rate_refuse_code_c.v refuse_code_addr_img) and
    returns 0. The premise r <= 4 is needed: the 32-bit `addiw` and refuse_code's 64-bit `bgeu` disagree when a1 has
    high bits set. On that path it writes a0-a3, stores ra in its frame [sp - 16, sp) and loads it back, and reads the
    table entry and the string (in the read-only segment at 0x10000: mem_inv makes those reads come from the image).

    Callee contract its walk takes as a premise: strcmp_contract (U/Prog/strcmp_c.v, STRCMP = 0x1d710; role's,
    relocated), with sx = sy = refuse_code_res r read from the image.

    Call sites (LLVMFuzzerTestOneInput, UBSan), with sp = S - 592 (the harness frame):
      0x145bc `jal check_code` in the two-pass decide loop, with a0 = reac_rate_refuse_code(r) (the call at 0x145b4
              with a0 = s5) and a1 = s5 = r (0x145b8 `mv a1,s5`), r = reac_rate_cfg_decide's result (0x14538);
      0x14610 `jal check_code` after the loop, with a0 = reac_rate_refuse_code(4) (the call at 0x14608) and a1 = 4
              (0x1460c `addi a1,zero,4`).
    Why each premise holds there: reac_rate_cfg_decide_contract gives r = Z_to_bv 64 (decide_res ...) with
    0 <= decide_res <= 3 (Pod/RateCfg.v decide_res_range), and 4 is 4; reac_rate_refuse_code_contract gives
    a0 = Z_to_bv 64 (refuse_code_addr (bv_unsigned r)). The stack region [lo, sp) with lo = S - 65536 is the frame's
    stack, writable and outside the image, and lo + 16 <= S - 592; mem_inv holds of the memory the cut runs on and
    every callee since keeps it. *)
Definition CHECK_CODE : Z := 0x14744.
Definition CHECK_CODE_FRAME : Z := 16.
Definition CODE_TBL : Z := 0x10634.

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

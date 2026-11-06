From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_refuse_code(r) (reac_rate_cfg.c:16-22; 60 bytes, 15 instructions at 0x14cd8 in the UBSan image):
      0x14cd8 addi a1,zero,4; bgeu a1,a0,0x14cec;
              auipc a0,0xffffb; addi a0,a0,0x701 (a0 = 0x14ce0 - 0x5000 + 0x701 = 0x103e1 = codes[0]); ret;
      0x14cec slli a2,a0,3; auipc a1,0xa; addi a1,a1,0xd0 (a1 = 0x14cf0 + 0xa000 + 0xd0 = 0x1edc0); not a3,a1;
              bltu a3,a2,0x14d10; slli a0,a0,3; add a0,a1,a0; ld a0,0(a0); ret;
      0x14d10 unimp (the pointer-overflow trap of codes + r).
    Unlike the plain image, codes[] stays an absolute pointer table: REFUSE_TBL = 0x1edc0 in .data.rel.ro (the rw
    segment at 0x1ecb8, under PT_GNU_RELRO [0x1ecb8, 0x1f000)) holds the five 8-byte pointers 0x103e1 "none",
    0x102d1 "not_closed", 0x10375 "not_drivable", 0x10400 "role_slave", 0x103d7 "malformed" (the plain image's
    string addresses; [refuse_tbl_img], [refuse_code_addr_img] check this by computation on the image).
    Total: for a0 <= 4 as a 64-bit unsigned word (the bgeu) it returns the 8 bytes at REFUSE_TBL + 8 a0 (ld), else
    codes[0] directly: refuse_code_addr (bv_unsigned a0), the address of the string refuse_code_res (bv_unsigned a0)
    (Pod/RateCfg.v). On the table path the trap branch tests ~REFUSE_TBL <u 8 a0; with 8 a0 <= 32 and
    ~REFUSE_TBL = 2^64 - 1 - 0x1edc0 it is never taken, so the contract needs no premise for it. It writes a0 and a1
    (4, or REFUSE_TBL on the table path) and, on the table path, a2 (8 a0) and a3 (~REFUSE_TBL); it stores nothing and
    uses no stack. It reads only the 8-byte entry at REFUSE_TBL + 8 a0. That segment is writable, so mem_inv does
    not fix those bytes: hence the table premise (the 40 table bytes read as the image's).

    Call sites (LLVMFuzzerTestOneInput, UBSan):
      0x145b4 `jal reac_rate_refuse_code` in the two-pass decide loop with a0 = s5 = reac_rate_cfg_decide's result
              (0x145b0 `mv a0,s5`; 0x14538 `mv s5,a0`); the result goes straight to check_code's a0 (0x145bc);
      0x14608 `jal reac_rate_refuse_code` after the loop with a0 = 4 (0x14604 `addi a0,zero,4`, MALFORMED); the
              result goes straight to check_code's a0 (0x14610).
    Why the premise holds there: rate_check_contract (U/Prog/LLVMFuzzerTestOneInput_c.v) takes the same fact for
    [REFUSE_TBL, REFUSE_TBL + 40) = [0x1edc0, 0x1ede8) of the memory its evt starts on; the table lies in
    frame_RELRO's first range [0x1ecb8, 0x1ecb8 + 448) (U/FrameAPI.v), so the slot's relro conjunct gives it at the
    cut. Between the evt's start and these calls the harness writes only its heap blocks and stack (the pod copy, the
    parse's frame and hz cell, the check frames), none of these 40 bytes. *)
Definition REAC_RATE_REFUSE_CODE : Z := 0x14cd8.
Definition REFUSE_TBL : Z := 0x1edc0.
Definition REFUSE_TBL_SIZE : Z := 40.
Definition CODE_NONE : Z := 0x103e1.
Definition CODE_NOT_CLOSED : Z := 0x102d1.
Definition CODE_NOT_DRIVABLE : Z := 0x10375.
Definition CODE_ROLE_SLAVE : Z := 0x10400.
Definition CODE_MALFORMED : Z := 0x103d7.

(** codes[] = REAC_RATE_REFUSE_CODES_INIT, the five pointers in the table. *)
Definition REFUSE_PTRS : list Z := [CODE_NONE; CODE_NOT_CLOSED; CODE_NOT_DRIVABLE; CODE_ROLE_SLAVE; CODE_MALFORMED].

(** The result for r = bv_unsigned a0: codes[r] for r <= 4, else codes[0]. *)
Definition refuse_code_addr (r : Z) : Z := nth (refuse_idx r) REFUSE_PTRS CODE_NONE.

Definition reac_rate_refuse_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    (forall a, REFUSE_TBL <= a < REFUSE_TBL + REFUSE_TBL_SIZE -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (refuse_code_addr (bv_unsigned a0))) a1' a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_REFUSE_CODE) fc None m (seg_rom rsegs)).

(** ** The image's bytes (computation on rsegs) *)

(** The n bytes of the image at a, as values. *)
Definition img_bytes (a : Z) (n : nat) : option (list Z) :=
  option_map (map bv_unsigned) (memory_read rsegs (Z_to_bv 64 a) (N.of_nat n)).

(** A little-endian value. *)
Definition le_val (l : list Z) : Z := fold_right (fun b acc => b + 256 * acc) 0 l.

(** The table: entry i is the pointer codes[i]. *)
Lemma refuse_tbl_img : forall i, (i < 5)%nat ->
  option_map le_val (img_bytes (REFUSE_TBL + 8 * Z.of_nat i) 8) = Some (nth i REFUSE_PTRS 0).
Proof.
  intros i Hi. destruct i as [|[|[|[|[|i]]]]]; [ | | | | | exfalso; lia]; vm_compute; reflexivity.
Qed.

(** The string each answer points to: refuse_code_res r and its NUL. *)
Lemma refuse_code_addr_img : forall r,
  img_bytes (refuse_code_addr r) (S (length (refuse_code_res r))) =
  Some (map bv_unsigned (refuse_code_res r ++ [Z_to_bv 8 0])).
Proof.
  intros r. unfold refuse_code_addr, refuse_code_res. pose proof (refuse_idx_lt r) as H.
  destruct (refuse_idx r) as [|[|[|[|[|k]]]]]; [ | | | | | exfalso; lia]; vm_compute; reflexivity.
Qed.

(** A control: the addresses are not the next byte over. *)
Lemma refuse_code_addr_img_control :
  img_bytes (CODE_NONE + 1) 5 <> Some (map bv_unsigned (refuse_code_res 0 ++ [Z_to_bv 8 0])).
Proof. vm_compute. discriminate. Qed.

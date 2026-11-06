From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_refuse_code(r) (reac_rate_cfg.c:16-22; 48 bytes, 12 instructions at 0x14990 in the plain image):
      0x14990 addi a1,zero,4; bgeu a1,a0,0x149a4;
              auipc a0,0xffffc; addi a0,a0,-0x5b7 (a0 = 0x14998 - 0x4000 - 0x5b7 = 0x103e1 = codes[0]); ret;
      0x149a4 slli a0,a0,2; auipc a1,0xffffc; addi a1,a1,-0x344 (a1 = 0x149a8 - 0x4000 - 0x344 = 0x10664);
              add a0,a1,a0; lw a0,0(a0); add a0,a1,a0; ret.
    The compiler turned `static const char *const codes[]` into a relative table in .rodata: REFUSE_TBL = 0x10664
    holds five signed 32-bit offsets from the table (-643, -915, -751, -612, -653), so codes[r] = 0x10664 + offset:
    0x103e1 "none", 0x102d1 "not_closed", 0x10375 "not_drivable", 0x10400 "role_slave", 0x103d7 "malformed", all in
    .rodata ([refuse_tbl_img], [refuse_code_addr_img] below check this by computation on the image).
    Total: for a0 <= 4 as a 64-bit unsigned word (the bgeu; the source's `(unsigned)r >= 5` on the sign-extended int)
    it returns REFUSE_TBL + the sign-extended entry a0 (lw), else codes[0] directly: refuse_code_addr (bv_unsigned a0),
    the address of the string refuse_code_res (bv_unsigned a0) (Pod/RateCfg.v). It writes a0 and a1 (4, or
    REFUSE_TBL on the table path), stores nothing and uses no stack. It reads only the 4-byte entry at
    REFUSE_TBL + 4 a0, in the read-only segment at 0x10000: mem_inv makes that read come from the image.

    Call sites (LLVMFuzzerTestOneInput, plain):
      0x144a0 `jal reac_rate_refuse_code` in the two-pass decide loop with a0 = s6 = reac_rate_cfg_decide's result
              (0x1449c `mv a0,s6`; 0x14424 `mv s6,a0`); the result goes straight to check_code's a0 (0x144a8);
      0x144f8 `jal reac_rate_refuse_code` after the loop with a0 = 4 (0x144f4 `addi a0,zero,4`, MALFORMED); the
              result goes straight to check_code's a0 (0x14500).
    Why the premise holds there: mem_inv holds of the memory the cut runs on and every callee since keeps it
    (each contract's post has mem_inv of its m'; this function and reac_rate_cfg_decide store nothing).
    refuse_code_addr is what check_code's premise names. *)
Definition REAC_RATE_REFUSE_CODE : Z := 0x14990.
Definition REFUSE_TBL : Z := 0x10664.
Definition CODE_NONE : Z := 0x103e1.
Definition CODE_NOT_CLOSED : Z := 0x102d1.
Definition CODE_NOT_DRIVABLE : Z := 0x10375.
Definition CODE_ROLE_SLAVE : Z := 0x10400.
Definition CODE_MALFORMED : Z := 0x103d7.

(** codes[] = REAC_RATE_REFUSE_CODES_INIT, as the table's five targets. *)
Definition REFUSE_PTRS : list Z := [CODE_NONE; CODE_NOT_CLOSED; CODE_NOT_DRIVABLE; CODE_ROLE_SLAVE; CODE_MALFORMED].

(** The result for r = bv_unsigned a0: codes[r] for r <= 4, else codes[0]. *)
Definition refuse_code_addr (r : Z) : Z := nth (refuse_idx r) REFUSE_PTRS CODE_NONE.

Definition reac_rate_refuse_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (refuse_code_addr (bv_unsigned a0))) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_REFUSE_CODE) fc None m (seg_rom rsegs)).

(** ** The image's bytes (computation on rsegs) *)

(** The n bytes of the image at a, as values. *)
Definition img_bytes (a : Z) (n : nat) : option (list Z) :=
  option_map (map bv_unsigned) (memory_read rsegs (Z_to_bv 64 a) (N.of_nat n)).

(** A little-endian value. *)
Definition le_val (l : list Z) : Z := fold_right (fun b acc => b + 256 * acc) 0 l.

(** The table: entry i is codes[i] - REFUSE_TBL, as a 32-bit word. *)
Lemma refuse_tbl_img : forall i, (i < 5)%nat ->
  option_map le_val (img_bytes (REFUSE_TBL + 4 * Z.of_nat i) 4) = Some ((nth i REFUSE_PTRS 0 - REFUSE_TBL) mod 2^32).
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

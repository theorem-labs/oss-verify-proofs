(** reac-pw/fuzz_segconf, UBSan build: what musl's printf family (snprintf_c.v and vsnprintf_c.v, the
    released P1/G2 forms) asks of every caller's machine, and the post form of a function that calls it. The
    contracts of reac_segconf's and the harness model's functions that print (refuse, cross_check,
    reac_segconf_parse_file, reac_segconf_parse, m_refuse, m_file) use these. Statement text only. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** This build's addresses. *)
Definition SA : seg_addrs := SEG_UBSAN.

(** The stack-protector cells musl's printf_core, strstr, strspn and strtol read: the GOT cell holds the guard's
    address, and the guard is a readable word (the frame's allocator statics give both). *)
Definition ssp_ok (m : word -> option byte) : Prop :=
  bytes_at rsegs m (sa_got_guard SA) (le8 (Z_to_bv 64 (sa_guard SA))) /\
  exists g : word, bytes_at rsegs m (sa_guard SA) (le8 g).

(** The machine printf needs (snprintf_c.v / vsnprintf_c.v premises): fcsr's rounding mode 0 (printf_core's
    dynamic-rounding instructions), the memory in MemNorm's normal form, the stack-protector cells, the stack region
    [lo, sp) above the image and below 2^63. *)
Definition printf_env (m : word -> option byte) (fc : bv 32) (lo sp : Z) : Prop :=
  frm0 fc /\ MemNorm.task_mem rsegs m /\ ssp_ok m /\ sa_img_end SA <= lo /\ sp < 2 ^ 63.

(** The post of a function that calls printf: as seg_spec.ret_post, but the FP registers other than fa0 (f10)
    and fcsr's rounding mode are what is kept (printf_core writes fa0 and accrues fflags), and the memory stays in
    MemNorm's normal form. *)
Definition ret_post_fp (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (r : Z) (m : word -> option byte) (W : list ivl) (lo : Z) (Q : (word -> option byte) -> Prop)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
    munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\ Q m'.
(** The same for a void function. *)
Definition ret_void_fp (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (m : word -> option byte) (W : list ivl) (lo : Z) (Q : (word -> option byte) -> Prop)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
    munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\ Q m'.

(** printf's per-call stack below its caller's sp (snprintf_c.v SNPRINTF_K 5936 >= vsnprintf_c.v VSNPRINTF_K 5856,
    released DIS numbers, the same in both builds). *)
Definition PRINTF_K : Z := 5936.

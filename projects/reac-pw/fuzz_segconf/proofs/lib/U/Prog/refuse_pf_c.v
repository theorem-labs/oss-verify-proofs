(** reac-pw/fuzz_segconf, UBSan build: the callee premises of refuse's two printf calls (snprintf 0x19a14 for the
    address prefix, vsnprintf 0x1e490 with refuse's va_list), stated in seg_env's terms, so that
    refuse's walk (U/Prog/refuse.v) can take them as hypotheses. U/Prog/refuse_pf.v proves them from the printf contracts
    snprintf_contract and vsnprintf_contract. Statement text only. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
Import ListNotations.
Open Scope Z_scope.

(** * refuse's two printf calls, as callee premises

    The printf contracts snprintf_contract and vsnprintf_contract (U/Prog/snprintf_c.v, U/Prog/vsnprintf_c.v, commit
    585d8ec7a43b) at refuse's call shapes, stated in seg_env's terms: printf_env for the
    machine, stack_ok for printf's stack, the format in .rodata, the arguments as seg_spec.va_args_ok, the text as
    SegModel.fmt (Spec/SegPrintfBridge.v relates printf_model to it), and the post as seg_env.ret_post_fp.
    U/Prog/refuse_pf.v proves both from the printf contracts: va_arg_ok's bounds (a string of at most 65535 bytes,
    an integer in [0, 2^31)) give printf_model's INT_MAX bound and SegPrintfBridge.sp_fit for the 19 formats. *)
Definition RF_SNPRINTF : Z := 0x19a14.
Definition RF_VSNPRINTF : Z := 0x1e490.

(** The destination [D, D + n): inside the refusal slot [Dslot, Dslot + 200), covered by no reserved segment of the
    image (blk_noimg: printf_facts_c.pf_img_free's text), present and writable, apart from [lo, hi). *)
Definition rf_dst (m : word -> option byte) (lo hi Dslot D n : Z) : Prop :=
  0 < D /\ 1 <= n /\ Dslot <= D /\ D + n <= Dslot + RC_REFUSAL_LEN /\ blk_noimg rsegs D n /\
  wr_at rsegs m D n /\ (exists junk, bytes_at rsegs m D junk /\ Z.of_nat (length junk) = n) /\ apart D n lo hi.

(** The format at fp, one of fs, in .rodata, and the arguments its conversions take, held by rs (strings apart
    from [lo, S) and from the slot). *)
Definition rf_fmt (m : word -> option byte) (lo S Dslot : Z) (fs : list (list Z)) (fp : Z) (f : list Z)
    (rs : list word) (args : list arg) : Prop :=
  In f fs /\ conv_kinds f = map arg_is_s args /\
  cstrz_at rsegs m fp f /\ RO_LO <= fp /\ fp + Z.of_nat (length f) + 1 <= sa_ro_end SA /\
  va_args_ok rsegs m [(lo, S); (Dslot, Dslot + RC_REFUSAL_LEN)] rs args.

(** What both calls return: a0 = snprintf_r f args; the text snprintf_s n f args and its NUL at D; they write only
    the stack region [lo, sp) and that text. *)
Definition rf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (m : word -> option byte) (lo D n : Z) (f : list Z) (args : list arg) : machine_state -> Prop :=
  ret_post_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (snprintf_r f args) m
    [(lo, bv_unsigned sp); (D, D + Z.of_nat (length (snprintf_s n f args)) + 1)] lo
    (fun m' => bytes_at rsegs m' D (zb (snprintf_s n f args) ++ [ZERO])).

(** snprintf(D, n, fmt, ...) for the address prefixes "%s:%d: " and "%s: ", the arguments in a3 .. a7. *)
Definition rf_snprintf : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo Dslot : Z) (f : list Z) (args : list arg),
    rf_fmt m lo (bv_unsigned sp) Dslot [F_addr_line; F_addr] (bv_unsigned a2) f [a3; a4; a5; a6; a7] args ->
    rf_dst m lo (bv_unsigned sp) Dslot (bv_unsigned a0) (bv_unsigned a1) ->
    printf_env m fc lo (bv_unsigned sp) -> stack_ok rsegs m lo (bv_unsigned sp) PRINTF_K -> mem_inv rsegs m ->
    evt rsegs
      (rf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo (bv_unsigned a0) (bv_unsigned a1) f args)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RF_SNPRINTF) fc None m (seg_rom rsegs)).

(** vsnprintf(D, n, fmt, ap) for the 17 refusal formats, ap = a3 the address of the caller's saved variadic
    slots (refuse: sp + 0x38, the five slots a3 .. a7). *)
Definition rf_vsnprintf : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo Dslot : Z) (f : list Z)
         (slots : list word) (args : list arg),
    rf_fmt m lo (bv_unsigned sp) Dslot REFUSE_FORMATS (bv_unsigned a2) f slots args ->
    saved_at rsegs m (bv_unsigned a3) slots -> bv_unsigned sp <= bv_unsigned a3 ->
    bv_unsigned a3 + 8 * Z.of_nat (length slots) < 2 ^ 63 ->
    rf_dst m lo (bv_unsigned a3 + 8 * Z.of_nat (length slots)) Dslot (bv_unsigned a0) (bv_unsigned a1) ->
    printf_env m fc lo (bv_unsigned sp) -> stack_ok rsegs m lo (bv_unsigned sp) PRINTF_K -> mem_inv rsegs m ->
    evt rsegs
      (rf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo (bv_unsigned a0) (bv_unsigned a1) f args)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RF_VSNPRINTF) fc None m (seg_rom rsegs)).

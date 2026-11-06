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

(** refuse(c, line, fmt, ...) (reac_segconf.c:30-48, static, variadic; at 0x15c80 in the UBSan image 1696d6c34ffd; frame 0x60:
    ra, s0-s2 at sp + 0x28 .. 0x10, the variadic a3 .. a7 spilled to sp + 0x38 .. 0x58, ap = sp + 0x38 at sp + 8).
    c->refused++ (`sw` c + 0x34cc); n_refusals >= 8 (`blt 7, n`) returns; else
    dst = c->refusal[n] (c + 0x2e88 + 200 n), where = c->reading[0] ? c->reading : "reac-pw.conf" (seg_spec.STR_BASE),
    k = snprintf(dst, 200, "%s:%d: ", where, line) for line > 0, else snprintf(dst, 200, "%s: ", where)
    (`jal snprintf`, 0x19a14); k > 199 as unsigned returns (the slot written, not kept); else
    vsnprintf(dst + k, 200 - k, fmt, ap) (`jal vsnprintf`, 0x1e490, with refuse's va_list: a format of the
    17 takes at most 3 slots, so it reads only [sp + 0x38, sp + 0x50)) and n_refusals++.
    UBSan (77 instructions): traps on c & 7 <> 0, on n_refusals >= 9 (the address of refusal[n], reached only for
    n <= 7), on c + 0x2e88 + 200 n wrapping, on dst + k wrapping and on n_refusals + 1 overflowing: c 16-aligned,
    n_refusals <= 8 (rconf_enc), the block inside the address space, 0 <= k <= 199.

    Post in the spine's terms: c holds SegModel.refuse rc line f args. It writes its frame and printf's stack below
    it, refused, and when n_refusals < 8 the slot refusal[n] and n_refusals (the slot even when k >= 200: rconf_enc
    leaves refusal[i] for i >= n_refusals unfixed; k >= 200 never
    happens for this harness's inputs: SegModel.refuse_rel).

    Callee contracts its walk takes as premises: snprintf_contract (Prog/snprintf_c.v under lib/U, the "%s:%d: "
    and "%s: " prefixes, exact text and return value) and vsnprintf_contract (Prog/vsnprintf_c.v under lib/U:
    the caller's va_list, exact text for the 17 formats; Spec/SegPrintfBridge.v relates printf_model to SegModel.fmt);
    their premises are printf_env, the format in .rodata, the %s arguments' slack and placement.

    Call sites: reac_segconf_parse_file 0x15440, 0x1569c, 0x15790, 0x15900, 0x15a68, 0x15a88 and 0x15bf8 (c, lineno >= 1, one of the 17 formats; the string arguments
    point into parse_file's buf, cur_name, known (parse_file's frame) or the c block; ints 511, 15, 32) and cross_check
    0x15f74 and 0x15f9c (c, 0, F_xmodel with s->name and s->model, F_xbox with s->name: fields of the c block). *)
Definition REFUSE : Z := 0x15c80.
Definition REFUSE_STACK : Z := 0x60 + PRINTF_K.

Definition refuse_pre (m : word -> option byte) (fc : bv 32) (sp lo c line fp : Z) (va : list word) (rc : rconf)
    (ln : Z) (f : list Z) (args : list arg) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ rconf_at rsegs m c rc /\ apart c SEG_C_SIZE lo sp /\ blk_noimg rsegs c SEG_C_SIZE /\
  rc_refused rc + 1 < 2 ^ 32 /\
  0 <= ln < 2 ^ 31 /\ line = ln /\
  In f REFUSE_FORMATS /\ conv_kinds f = map arg_is_s args /\
  fp <> 0 /\ cstrz_at rsegs m fp f /\ RO_LO <= fp /\ fp + Z.of_nat (length f) + 1 <= sa_ro_end SA /\
  va_args_ok rsegs m
    [(lo, sp); (refusal_addr c (length (rc_refusal rc)), refusal_addr c (length (rc_refusal rc)) + RC_REFUSAL_LEN);
     (c + RC_REFUSED, c + RC_REFUSED + 4)] va args /\
  printf_env m fc lo sp /\ stack_ok rsegs m lo sp REFUSE_STACK /\ mem_inv rsegs m.

(** The bytes it writes. *)
Definition refuse_W (sp c : Z) (rc : rconf) : list ivl :=
  [(sp - REFUSE_STACK, sp); (c + RC_REFUSED, c + RC_REFUSED + 4)] ++
  (if (length (rc_refusal rc) <? 8)%nat
   then [(refusal_addr c (length (rc_refusal rc)), refusal_addr c (length (rc_refusal rc)) + RC_REFUSAL_LEN);
         (c + RC_NREF, c + RC_NREF + 4)]
   else []).

Definition refuse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo ln : Z) (rc : rconf) (f : list Z) (args : list arg),
    refuse_pre m fc (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) [a3; a4; a5; a6; a7] rc ln f args ->
    evt rsegs
      (ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
         m
         (refuse_W (bv_unsigned sp) (bv_unsigned a0) rc)
         lo
         (fun m' => rconf_at rsegs m' (bv_unsigned a0) (refuse rc ln f args)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REFUSE) fc None m (seg_rom rsegs)).

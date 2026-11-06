From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Spa Rate.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_prop_parse(props, out_hz) (reac_rate_cfg.c:115-152; 628 bytes, 157 instructions at 0x14c58 in the plain
    image; frame 0x50 bytes, saves ra, s0-s7 at sp - 8 .. sp - 72, s0 = out_hz).
      - props = NULL (0x14c58 `beqz a0`): returns -1 at 0x14d28 with no frame, no store.
      - spa_pod_is_object_type: S = u32 at props; S >= 2^20, S < 8, type <> 15 (Object) or object type <> 0x40002
        (Props) return -1. Then spa_pod_object_find_prop walks the props from props + 16 (loop 0x14cd8-0x14d24,
        bounds of spa_pod_prop_is_inside against S); no key 0x80001 (SPA_PROP_params), or a value that is not a
        Struct with size in [8, 2^20), returns 0. Then SPA_POD_STRUCT_FOREACH (loop 0x14d78-0x14de4) pairs keys and
        values: a String child opens the key slot; the next child is its value when strcmp(key, "reac.cfg.rate") = 0
        (0x14dc4 `jal` strcmp 0x1d328; the literal at 0x1045e in .rodata, Pod/RateImg.v rate_key_plain); an Int value
        stores its 32 bits at out_hz (0x14e0c `sw a0,0(s0)`) and returns 1; a Float value read as its nearest integer
        (reac_float_near.h, inlined: fcvt.d.s, fadd.d with the dynamic rounding mode, fle.d, flt.d, fcvt.l.d rtz,
        fcvt.d.l, flt.d, sub) stores it there and returns 1 when it lies in [INT_MIN, INT_MAX], else returns -1; any
        other value returns -1; the end of the Struct returns 0.
    That is Rate.parse_model on the len bytes at props (Pod/Rate.v), and Rate.harness_parse for the harness's NULL
    flag. Every read lies in [props, props + len) (each pass is guarded by a test against the top size word
    S = len - 8, which the corruption never writes), plus .rodata (the literal; the double constants) and its frame (the
    float temp at sp). It writes its frame [sp - 0x50, sp) and, only when it returns 1, the 4 bytes at out_hz. It
    writes the integer registers a0-a6 (and strcmp's a0-a3) and the FP registers fa3, fa4, fa5 (f13-f15), and only
    accrues fflags: frm stays as it was. The two dynamic-rounding instructions need frm = 0 (rm 7 with frm 5..7 is an
    illegal instruction): hence frm0 fc. The return value is 1, 0 or -1 as a 64-bit word (-1 = 2^64 - 1); the value
    stored is the low 32 bits of the int, le4 of its sign extension.

    Callee contract its walk takes as a premise: strcmp_contract (Prog/strcmp_c.v, STRCMP = 0x1d328; role's,
    relocated).

    Call site (LLVMFuzzerTestOneInput, plain): 0x14224 `jal reac_rate_prop_parse` with sp = S0 - 544 (the harness
    frame) and
      a0 = 0 if flags bit 0 else pod (0x1420c `andi s1,s6,1`, 0x14218 `addi a0,s1,-1`, 0x1421c `and a0,a0,s3`;
           s3 = pod, the result of malloc(len + (len = 0)) at 0x141e0, into which memcpy(pod, pp->buf, len) at
           0x141fc copied pp->buf[0..len), skipped when len = 0 (0x141ec `beqz s4`));
      a1 = sp + 0x158, the hz cell, set to 0x5a5a5a5a at 0x14214 (0x14208 `lui`, 0x14210 `addi`).
    Why each premise holds there (rate_check_contract, the M02 segment from the cut 0x141e4): bs = pp->buf[0..len) =
    Pod.Model.buf of the pod_build record (the memcpy's post); len >= 8 (pod_build's first two pod_put32 always
    succeed) and the first 4 bytes hold len - 8 (the top patch; the corruption writes only offsets 8 .. len - 1);
    P = pod is a malloc result: nonzero and 16-aligned, and the block lies below lo = S0 - 65536 (the frame's stack
    region), so P + len <= lo; Q = sp + 0x158 is 4-aligned and writable in the harness frame, above this sp; the
    stack region [lo, sp) is the frame's (stk, writable, outside the image); frm0 fc is the slot's FP invariant;
    mem_inv holds of the memory the cut runs on. The answer is what Pod/Rate.v's harness_parse_build relates to
    expect_rate on an uncorrupted pod, and its fst says what the cell holds after. *)
Definition REAC_RATE_PROP_PARSE : Z := 0x14c58.
Definition PARSE_FRAME : Z := 0x50.

(** What the caller supplies: the len bytes bs of the pod at P (16-aligned, nonzero, with its top size word len - 8
    and len >= 8), below the stack region [lo, sp); the 4-byte hz cell at Q, writable, 4-aligned, at or above sp.
    The pod bytes are used only when the argument is not NULL. *)
Definition rate_args (m : word -> option byte) (lo sp P Q : Z) (bs : list byte) : Prop :=
  bytes_at rsegs m P bs /\ 0 < P /\ P mod 16 = 0 /\
  8 <= Z.of_nat (length bs) /\ u32_at bs 0 = Z.of_nat (length bs) - 8 /\
  P + Z.of_nat (length bs) <= lo /\
  wr_at rsegs m Q 4 /\ Q mod 4 = 0 /\ sp <= Q.

(** Memory after the call: the frame below sp, and on a written value v the 4 bytes of v at Q. *)
Definition rate_mem (m m' : word -> option byte) (sp Q : Z) (w : option Z) : Prop :=
  match w with
  | Some v => munch [(sp - PARSE_FRAME, sp); (Q, Q + 4)] m m' /\ bytes_at rsegs m' Q (le4 (Z_to_bv 64 v))
  | None => munch [(sp - PARSE_FRAME, sp)] m m'
  end.

Definition rate_prop_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (null : bool) (lo P Q : Z) (bs : list byte),
    a0 = Z_to_bv 64 (if null then 0 else P) -> a1 = Z_to_bv 64 Q ->
    rate_args m lo (bv_unsigned sp) P Q bs ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PARSE_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (snd (harness_parse null bs)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         (forall k : bv 5, ~ (13 <= bv_unsigned k <= 15) -> Sem.reg_get F' k = Sem.reg_get F k) /\
         frm0 fc' /\
         rate_mem m m' (bv_unsigned sp) Q (fst (harness_parse null bs)) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_PROP_PARSE) fc None m (seg_rom rsegs)).

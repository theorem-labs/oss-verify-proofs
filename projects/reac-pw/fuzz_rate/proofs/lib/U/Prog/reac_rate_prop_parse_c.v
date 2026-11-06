From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Spa Rate.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_prop_parse(props, out_hz) (reac_rate_cfg.c:115-152; 716 bytes, 179 instructions at 0x14fe8 in the UBSan
    image; frame 0x50 bytes, made at entry before the NULL test: saves ra, s0-s7 at sp - 8 .. sp - 72, s0 = out_hz).
      - props = NULL (0x15010 `beqz a0`): returns -1 through the epilogue, no store outside the frame.
      - props not 4-aligned (0x1501c `bnez a1` after `andi a1,a0,3`): the trap (0x152b0 unimp); the premise
        P mod 16 = 0 makes it dead. Then the same SPA walk as the plain image (Prog/reac_rate_prop_parse_c.v), with
        the UBSan alignment and pointer-overflow tests (10 trap branches to 0x152b0), each dead when every read lies in
        [props, props + len) with props + len <= lo < 2^64: strcmp(key, "reac.cfg.rate") (0x1516c -> 0x1d710; the
        literal at 0x1045e, Pod/RateImg.v rate_key_ubsan); an Int value stores its 32 bits at out_hz (0x151c0
        `sw a0,0(s0)`) and returns 1; a Float value read as its nearest integer (fcvt.d.s, fadd.d with the dynamic
        rounding mode, fle.d / flt.d range tests, fcvt.l.d rtz, fcvt.d.l, flt.d) stores it and returns 1 when it lies
        in [INT_MIN, INT_MAX], else -1; any other value -1; the end of the Struct 0.
    That is Rate.harness_parse on the len bytes at props (Pod/Rate.v). It writes its frame [sp - 0x50, sp) and, only
    when it returns 1, the 4 bytes at out_hz; it writes the integer registers a0-a6 (and strcmp's a0-a3) and the FP
    registers fa3, fa4, fa5 (f13-f15), and only accrues fflags: frm stays as it was; the dynamic-rounding instructions
    need frm = 0: hence frm0 fc. The return value is 1, 0 or -1 as a 64-bit word.

    Callee contract its walk takes as a premise: strcmp_contract (U/Prog/strcmp_c.v, STRCMP = 0x1d710; role's,
    relocated).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14244 `jal reac_rate_prop_parse` with sp = S0 - 592 (the harness
    frame) and
      a0 = 0 if flags bit 0 else pod (0x1422c `andi s0,s2,1`, 0x14238 `addi a0,s0,-1`, 0x1423c `and a0,a0,s3`;
           s3 = pod, the result of malloc(len + (len = 0)) at 0x14208, into which memcpy(pod, pp->buf, len) at
           0x14224 copied pp->buf[0..len), skipped when len = 0 (0x14214 `beqz s4`));
      a1 = sp + 0x188, the hz cell, set to 0x5a5a5a5a at 0x14234 (0x14228 `lui`, 0x14230 `addi`).
    Why each premise holds there: as in the plain image (rate_check_contract, the M02 segment from the cut 0x1420c). *)
Definition REAC_RATE_PROP_PARSE : Z := 0x14fe8.
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

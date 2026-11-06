From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Spa Role.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_prop_parse(props, out_role) (reac_role_cfg.c:63-104; 732 bytes, 183 instructions at 0x14648 in the
    UBSan image; frame 0x50 bytes, saves ra, s0-s7 at sp-8 .. sp-72 before anything else, then s0 = out_role). The
    plain logic (lib/Prog/reac_role_prop_parse_c.v) with these differences: the prologue runs before the NULL test
    (0x14670 `beqz a0` -> 0x148ec: a1 = -1, a0 = a1, epilogue), so a NULL argument stores the spills too; the
    plain alignment returns of the find loop setup and the Struct test are traps here; the Int value is classified
    by `sext.w` and two compares (0x14814-0x14824); reac_float_nearest (0x1488c-0x148e8) adds the two float-cast
    bounds and the `r--` overflow check; the result is moved from a1 at 0x148f0. strcmp is 0x1cb44, the literal
    "reac.cfg.role" is at 0x1032e, the doubles at 0x104f8 (0.5), 0x10530 (-2^31), 0x104d8 (2^31), 0x10538
    (0xc3e0000000000001) and 0x104e8 (2^63), all in .rodata. Reads, writes, registers and the FP state as in the
    plain text: frame [sp - 0x50, sp), the 4 bytes at out_role only on a return of 1, integer registers a0-a6, FP
    registers fa3-fa5 (f13-f15), fflags accrued, frm unchanged; the dynamic-rounding fadd.d and fcvt.d.l need frm0.
    The ten trap branches (all to the `unimp` at 0x14920) and the premise that makes each dead:
      - 0x1467c `andi a1,a0,3; bnez`: props 4-aligned (P mod 16 = 0);
      - 0x1471c `andi a0,a2,3; bnez`: the found prop R = P + 16 + 8k (the find loop returns 0 at 0x14710 on a
        misaligned next pointer, which P mod 16 = 0 never gives);
      - 0x1476c `beqz s2`: the Struct child pointer C >= P + 24 > 0 (no wrap: P + len <= lo < 2^64);
      - 0x147a0 `bltu a1,a0` and 0x147b0 `beqz a2` (spa_pod_body_get_string's s[size - 1]): 1 <= CS < 2^20 was
        tested at 0x14780/0x14788, and C + 8 + CS - 1 < P + len does not wrap;
      - 0x14828 `beqz s0` and 0x14830 `andi a1,s0,3; bnez` (the store to *out_role): Q > 0 (sp <= Q, and sp > lo >= 0)
        and Q mod 4 = 0;
      - 0x148b8 and 0x148c8 (the bounds of `(long long)d`): reached only after -2^31 <= d < 2^31 (0x14894, 0x148a4);
      - 0x148e0 `bge a1,a0` (`r--`): reached only when d < t, so t >= -2^31 + 1.

    Callee contract its walk takes as a premise: strcmp_contract (U/Prog/strcmp_c.v, STRCMP = 0x1cb44; the released
    UBSan form of libreac/fuzz_ctrl, relocated).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x13f6c `jal reac_role_prop_parse` with sp = S - 544 (the harness
    frame) and
      a0 = 0 if flags bit 0 else pod (0x13f58 `andi s0,s3,1` with s3 = flags reloaded from 0x10(sp) at 0x13f34,
           `addi a0,s0,-1`, `and a0,a0,s1`; s1 = pod, the result of malloc(len) at 0x13f30, into which
           memcpy(pod, pp, len) at 0x13f50 copied pp->buf[0..len));
      a1 = sp + 0x158, the role cell, set to 0x5a (ROLE_UNSET) at 0x13f5c.
    Why each premise holds there: as in the plain build (bs = Pod.Model.buf of the record, len >= 8, its first 4
    bytes len - 8; P a malloc result below lo = S - 65536; Q = sp + 0x158 4-aligned and writable in the harness frame;
    stk, frm0, mem_inv from the cut). *)
Definition REAC_ROLE_PROP_PARSE : Z := 0x14648.
Definition PARSE_FRAME : Z := 0x50.

(** What the caller supplies: the len bytes bs of the pod at P (16-aligned, nonzero, with its top size word len - 8
    and len >= 8), below the stack region [lo, sp); the 4-byte role cell at Q, writable, 4-aligned, at or above sp.
    The pod bytes are used only when the argument is not NULL. *)
Definition role_args (m : word -> option byte) (lo sp P Q : Z) (bs : list byte) : Prop :=
  bytes_at rsegs m P bs /\ 0 < P /\ P mod 16 = 0 /\
  8 <= Z.of_nat (length bs) /\ u32_at bs 0 = Z.of_nat (length bs) - 8 /\
  P + Z.of_nat (length bs) <= lo /\
  wr_at rsegs m Q 4 /\ Q mod 4 = 0 /\ sp <= Q.

(** The answer: (None, -1) for a NULL argument, else parse_model of the pod bytes. *)
Definition parse_res (null : bool) (bs : list byte) : option role * Z :=
  if null then (None, -1) else parse_model bs.

(** Memory after the call: the frame below sp, and on a role the 4 bytes of role_z at Q. *)
Definition role_mem (m m' : word -> option byte) (sp Q : Z) (o : option role) : Prop :=
  match o with
  | Some r => munch [(sp - PARSE_FRAME, sp); (Q, Q + 4)] m m' /\ bytes_at rsegs m' Q (le4 (Z_to_bv 64 (role_z r)))
  | None => munch [(sp - PARSE_FRAME, sp)] m m'
  end.

Definition reac_role_prop_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (null : bool) (lo P Q : Z) (bs : list byte),
    a0 = Z_to_bv 64 (if null then 0 else P) -> a1 = Z_to_bv 64 Q ->
    role_args m lo (bv_unsigned sp) P Q bs ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PARSE_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (snd (parse_res null bs)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         (forall k : bv 5, ~ (13 <= bv_unsigned k <= 15) -> Sem.reg_get F' k = Sem.reg_get F k) /\
         frm0 fc' /\
         role_mem m m' (bv_unsigned sp) Q (fst (parse_res null bs)) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_ROLE_PROP_PARSE) fc None m (seg_rom rsegs)).

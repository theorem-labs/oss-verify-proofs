From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Spa Role.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_prop_parse(props, out_role) (reac_role_cfg.c:63-104; 636 bytes, 159 instructions at 0x14410 in the plain
    image; frame 0x50 bytes, saves ra, s0-s7 at sp-8 .. sp-72, s0 = out_role).
      - props = NULL (0x14410 `beqz a0`): returns -1 at 0x144e0 with no frame, no store.
      - spa_pod_is_object_type (body.h:427, iter.h:239): S = u32 at props; S >= 2^20, S < 8, type <> 15 (Object) or
        object type <> 0x40002 (Props) return -1. Then spa_pod_object_find_prop (iter.h:247-265, its second loop
        compiled away) walks the props from props + 16 (loop 0x14498-0x144dc, bounds of spa_pod_prop_is_inside,
        defs.h:329-332, against S); no key 0x80001 (SPA_PROP_params), or a value that is not a Struct with size in
        [8, 2^20), returns 0. Then SPA_POD_STRUCT_FOREACH (loop 0x1452c-0x1459c, iter.h:31-42) pairs keys and values
        (reac_role_cfg.c:79-102): a String child (spa_pod_get_string, body.h:224-237) opens the key slot; the next
        child is its value when strcmp(key, "reac.cfg.role") = 0 (0x1457c `jal` strcmp 0x1c8ac; the literal at
        0x1032e in .rodata); an Int value (body.h:165-173) or a Float value read as its nearest integer
        (reac_float_near.h:24-34, inlined: fcvt.d.s, fadd.d with the dynamic rounding mode, fle.d, flt.d, fcvt.l.d rtz,
        fcvt.d.l with the dynamic rounding mode, flt.d, subw) of 0 or 1 stores it at out_role (0x145d0 `sw`) and
        returns 1; any other value returns -1; the end of the Struct returns 0.
    That is Role.parse_model on the len bytes at props. Every read lies in [props, props + len): each pass is guarded
    by a test against the top size word S = len - 8 alone (the corruption never writes bytes 0..7),
    plus .rodata (the literal; the doubles 0.5 at 0x104f0, -2^31 at 0x10528, 2^31 at 0x104d8) and its frame (the
    float temp at sp). It writes its frame [sp - 0x50, sp) and, only when it returns 1, the 4 bytes at out_role. It
    writes the integer registers a0-a6 (and strcmp's a0-a3) and the FP registers fa3, fa4, fa5 (f13-f15), and only
    accrues fflags: frm stays as it was (no instruction of the image writes frm). The two dynamic-rounding
    instructions need frm = 0 (rm 7 with frm 5..7 is an illegal instruction): hence frm0 fc. The return value is
    1, 0 or -1 as a 64-bit word (-1 = 2^64 - 1).

    Callee contract its walk takes as a premise: strcmp_contract (Prog/strcmp_c.v, STRCMP = 0x1c8ac; the released
    form of libreac/fuzz_ctrl, relocated: both strings NUL-terminated, r = 0 <-> sx = sy, no stack, no store).

    Call site (LLVMFuzzerTestOneInput, plain): 0x13f84 `jal reac_role_prop_parse` with sp = S - 496 (the harness
    frame) and
      a0 = 0 if flags bit 0 else pod (0x13f70 `andi s3,s5,1`, `addi a0,s3,-1`, `and a0,a0,s1`; s1 = pod, the result
           of malloc(len) at 0x13f48, into which memcpy(pod, pp, len) at 0x13f64 copied pp->buf[0..len));
      a1 = sp + 0x128, the role cell, set to 0x5a (ROLE_UNSET) at 0x13f74.
    Why each premise holds there: bs = pp->buf[0..len) = Pod.Model.buf of the record (the memcpy's post); len >= 8
    (pod_build's first two pod_put32 always succeed) and the first 4 bytes hold len - 8 (the top patch, pod.h:440;
    the corruption writes only offsets 8 .. len - 1, pod.h:441-447); P = pod is a malloc result: nonzero and 16-aligned
    (malloc_ret), and the block lies below alloc_ceiling <= lo = S - 65536 (the frame's stack region), so
    P + len <= lo; Q = sp + 0x128 is 4-aligned and writable in the harness frame, at or above this sp; the stack
    region [lo, sp) is the frame's (stk, writable, outside the image); frm0 fc is the slot's FP invariant (the frame
    starts with frm = 0 and no instruction writes frm); mem_inv holds of the memory the cut runs on. *)
Definition REAC_ROLE_PROP_PARSE : Z := 0x14410.
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

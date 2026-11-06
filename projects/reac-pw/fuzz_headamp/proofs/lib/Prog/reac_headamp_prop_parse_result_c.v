From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** reac_headamp_prop_parse_result(props, out, max, res) (reac-pw f86a30a3 src/reac_headamp_prop.c:108-182; 1016
    bytes, 254 instructions at 0x1487c in the plain image; frame 0xa0 bytes, saves ra, s0-s11 at sp - 8 .. sp - 104
    and fs0 at sp - 112, then s0 = res, s2 = max, s3 = out). Its paths:
      - res <> 0: res->n = res->keys = res->refusal = 0 (0x148c8-0x148d0), before anything else;
      - props = NULL (0x148d8 `beqz a0`): returns -1;
      - spa_pod_is_object_type (body.h:427, iter.h:239) on S = the u32 at props: S >= 2^20, S < 8, type <> 15 or
        object type <> 0x40002 return -1; spa_pod_object_find_prop's loop (0x14938-0x14970) for key 0x80001, then
        spa_pod_is_struct: no such prop or not a Struct returns 0 (no second res store);
      - SPA_POD_STRUCT_FOREACH (0x14a28-0x14c70): a String child opens the key slot (spa_pod_get_string); the next
        child's key is tested by strncmp(key, "reac.headamp.", 13) (0x14a8c, strncmp 0x1d80c), keys++, then
        parse_key: strtol(key + 13, &dot, 10) (0x14acc, strtol 0x1c998; dot at sp + 0x28 of its frame), the '.'
        test, strcmp against "phantom" / "pad" / "sens" (0x1d744, up to three calls), the channel range; then
        value_pod_to_byte (spa_pod_get_bool / _int / _float with reac_float_nearest inlined: fcvt.d.s, fadd.d with
        the dynamic rounding mode, fle.d, flt.d, fcvt.l.d rtz, fcvt.d.l with the dynamic rounding mode) and
        value_in_range; a refusal keeps the first one; a good cell at n >= max ends the walk, else
        out[n] = (ch, param, value) by three `sb` (0x14bac-0x14bb4) and n++;
      - res <> 0: res->n = n, res->keys, res->refusal (0x149a4-0x149ac); returns n.
    That is Pod/Headamp.v's parse_props (NULL or the pod bytes) on the len bytes at props: every pod read lies in
    [props, props + 8 + S) and S = len - 8 (the top size word; the harness's corruption never writes bytes 0..7,
    pod.h:441-447), plus .rodata (the prefix and the three names, the doubles 0.5 and 256.0) and its frame. It writes
    its frame [sp - 0xa0, sp) and, through strtol (frame 0x120) and __intscan (frame 0x50), the stack down to
    sp - PARSE_STACK, the end pointer (in its own frame), errno at tp - 164 (strtol: EINVAL on no digit, ERANGE on
    overflow); the n cells out[0, 3n) (n <= max: out[max], the guard cell, is never written); res (12 bytes) only
    when res <> 0. It writes the caller-saved integer registers (it, strncmp, strtol, strcmp) and the FP registers
    (fa4, fa5 and fs0, which it restores; strtol and the string calls keep F): stated free, as fflags, with the
    rounding mode kept (no instruction of the image writes frm; the two dynamic-rounding instructions need frm = 0:
    frm0 fc). The SSP canary of strtol (its GOT slot and the guard) is read, never written.

    Callee contracts its walk takes as premises (statement text in this directory or on its branch):
      - strtol_contract (Prog/strtol_c.v, STRTOL = 0x1c998: plugin-hostd/fuzz_command's
        released form relocated; SSP GOT 0x1eea8 -> guard 0x50490, errno tp - 164, 368 bytes of stack), with
        Pod/Strtol.v's s10_val / s10_end / s10_errno, which Pod/Headamp.v's parse_key reads;
      - strncmp_contract (Prog/strncmp_c.v, STRNCMP = 0x1d80c; hostd's, BYTES-EQUAL:
        Spec/StrFun.v strncmp_model, no store, no stack);
      - strcmp_contract (Prog/strcmp_c.v, STRCMP = 0x1d744: fuzz_role's relocated
        libreac/fuzz_ctrl form: r = 0 <-> sx = sy, no store, no stack);
      - Prog/ParseFP.v (fuzz_role's verbatim): rfn_hw_nearest (reac_float_nearest's double
        instructions = Pod/Nearest.v nearest b 0 255, lo = 0, hi = 255), rfn_hw_t_range, with the two constant words
        f64_is_int (+0.0 = fmv.d.x of zero) 0 and f64_is_int 0x4070000000000000 256;
      - Pod/SpaBool.v spa_get_bool (spa_pod_get_bool), Pod/Spa.v spa_get_int / spa_get_float / spa_get_string.
    Prog/ParseSites.v states, for each of these call sites, what the walk must show there (strtol_site, pod_kept,
    lits_at).

    Call sites (LLVMFuzzerTestOneInput, plain), sp = S - 560 (the harness frame):
      0x140bc `jal reac_headamp_prop_parse_result` with
        a0 = s5 = (null ? 0 : pod) (0x140a4 `addi a0,s7,-1`, 0x140a8 `and s5,a0,s1`; s7 = the first input byte & 1,
             s1 = pod, the result of malloc(len) at 0x14048 into which memcpy(pod, pp, len) at 0x14068 copied
             pp->buf[0, len));
        a1 = s3 = out (malloc(3cap + 3) at 0x1407c, then memset(out, 0xa5, 3cap + 3) at 0x14090);
        a2 = s2 = cap (0x14054 `andi s2,s6,0xff`: the second input byte mod 10);
        a3 = sp + 0x150 = &res (0x140ac), its 12 bytes set to 0x5a at 0x1409c-0x140a0 (`sd`, `sw`);
      and, with res = NULL, through reac_headamp_prop_parse (Prog/reac_headamp_prop_parse_c.v) at 0x141a0.
    Why each premise holds there: bs = pp->buf[0, len) = Pod.Model.buf of the record (memcpy's post); 8 <= len <=
    5440 <= 16384 (pod_build_wf) and its first 4 bytes hold len - 8 (the top patch, pod.h:440); pod and out are
    malloc results: nonzero and 16-aligned (malloc_ret), live blocks apart from each other and below the stack
    region [lo, sp) with lo = S - 65536 (alloc_ceiling + SLOT_K <= S, GV); 0 <= cap <= 9; res = sp + 0x150 lies in
    the harness frame at or above this sp and is 4-aligned; errno is the frame's errno cell (FR: writable; in the
    image, apart from the stack and the heap); the SSP GOT slot and the guard are the frame's ms_got_guard and
    ms_guard (relro, image statics; strtol only reads them); the stack region is the frame's (stk, writable,
    outside the image) with lo + 528 <= S - 560; frm0 fc is the slot's FP invariant (frm_zero at every cut);
    mem_inv holds of the memory the cut runs on. Prog/HeadSites.v parse_site_check and parse_site_plain derive them at
    both sites from the premises of headamp_check_contract and headamp_plain_contract. *)
Definition HA_PARSE_RESULT : Z := 0x1487c.
Definition PARSE_FRAME : Z := 0xa0.
(* The deepest stack below the caller's sp: the parse's frame, strtol's 0x120 and __intscan's 0x50 (strncmp, strcmp
   and __shlim use none; __shgetc is dead for a string FILE). *)
Definition PARSE_STACK : Z := 0xa0 + 0x120 + 0x50.
(* strtol's SSP canary: the GOT slot that holds the guard's address, and the guard (hostd's strtol_c.v names,
   relocated). *)
Definition PARSE_SSP_GOT : Z := 0x1eea8.
Definition PARSE_SSP_GUARD : Z := 0x50490.
(* errno: __errno_location is `mv a0,tp; addi a0,a0,-0xa4` (0x162f0); strtol_c.v writes it as tp + -164. *)
Definition PARSE_ERRNO (tp : word) : Z := bv_unsigned tp + -164.

(** The props argument: NULL (the harness's null flag) or the pod bytes. *)
Definition parse_arg (null : bool) (bs : list byte) : option (list byte) := if null then None else Some bs.

(** Every region the parse writes, by the caller's sp: its stack, out[0, 3n), errno, and res when not NULL. *)
Definition parse_writes (sp O n E R : Z) : list ivl :=
  [(sp - PARSE_STACK, sp); (O, O + 3 * n); (E, E + 4)] ++ (if R =? 0 then [] else [(R, R + 12)]).
(** The regions it may write, for the disjointness premises: the stack region, the whole out block, errno, res. *)
Definition parse_space (lo sp O cap E R : Z) : list ivl :=
  [(lo, sp); (O, O + 3 * (cap + 1)); (E, E + 4)] ++ (if R =? 0 then [] else [(R, R + 12)]).

(** What the caller supplies: the len bytes bs of the pod at P (16-aligned, nonzero, len in [8, 16384], the top size
    word len - 8), below the stack region; the out block of 3 (cap + 1) writable bytes at O, below the stack region
    and apart from the pod; 0 <= cap <= 9; res = 0 or 12 writable 4-aligned bytes at or above sp; the errno cell; the
    SSP GOT slot and guard; every region read (the pod, the SSP cells) apart from every region written. *)
Definition parse_args (m : word -> option byte) (lo sp : Z) (tp : word) (P O cap R : Z) (bs : list byte)
    (ev can : word) : Prop :=
  bytes_at rsegs m P bs /\ 0 < P /\ P mod 16 = 0 /\
  8 <= Z.of_nat (length bs) <= 16384 /\ u32_at bs 0 = Z.of_nat (length bs) - 8 /\
  P + Z.of_nat (length bs) <= lo /\
  0 <= cap <= 9 /\ 0 < O /\ wr_at rsegs m O (3 * (cap + 1)) /\ O + 3 * (cap + 1) <= lo /\
  (O + 3 * (cap + 1) <= P \/ P + Z.of_nat (length bs) <= O) /\
  (R = 0 \/ (wr_at rsegs m R 12 /\ R mod 4 = 0 /\ sp <= R)) /\
  rw_cells rsegs m (PARSE_ERRNO tp) [C4 ev] /\
  disjoint_from [(lo, sp); (P, P + Z.of_nat (length bs)); (O, O + 3 * (cap + 1))] (PARSE_ERRNO tp) 4 /\
  (R = 0 \/ disjoint_from [(PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] R 12) /\
  bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) /\
  bytes_at rsegs m PARSE_SSP_GUARD (le8 can) /\
  disjoint_from (parse_space lo sp O cap (PARSE_ERRNO tp) R) PARSE_SSP_GOT 8 /\
  disjoint_from (parse_space lo sp O cap (PARSE_ERRNO tp) R) PARSE_SSP_GUARD 8.

(** The machine state after the return, for the answer o = parse_props (parse_arg null bs) cap: a0 = rc, the
    callee-saved registers and ra, sp, gp, tp kept, any caller-saved register, any FP state with frm kept 0; written
    only the regions of parse_writes; out[0, 3n) = the cells; res = (n, keys, refusal) when R <> 0; errno some value,
    still a writable cell. *)
Definition parse_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (lo O R : Z) (o : answer) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ans_rc o)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    munch (parse_writes (bv_unsigned sp) O (Z.of_nat (length (ans_cells o))) (PARSE_ERRNO tp) R) m m' /\
    bytes_at rsegs m' O (ha_cells_bytes (ans_cells o)) /\
    (R <> 0 -> bytes_at rsegs m' R (ans_res_bytes o)) /\
    rw_cells rsegs m' (PARSE_ERRNO tp) [C4 ev'] /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Definition reac_headamp_prop_parse_result_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (null : bool) (lo P O cap R : Z)
         (bs : list byte) (ev can : word),
    a0 = Z_to_bv 64 (if null then 0 else P) -> a1 = Z_to_bv 64 O -> a2 = Z_to_bv 64 cap -> a3 = Z_to_bv 64 R ->
    parse_args m lo (bv_unsigned sp) tp P O cap R bs ev can ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PARSE_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m ->
    evt rsegs
      (parse_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo O R (parse_props (parse_arg null bs) cap))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HA_PARSE_RESULT) fc None m (seg_rom rsegs)).

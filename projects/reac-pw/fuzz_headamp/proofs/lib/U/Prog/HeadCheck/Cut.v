(** The internal statements of the checking segment's walk (UBSan LLVMFuzzerTestOneInput, segment M03 of
    U/Prog/LLVMFuzzerTestOneInput_c.v's headamp_check_contract, [0x14118, 0x147dc)): the plain file's three pieces
    (Prog/HeadCheck/Cut.v) with the UBSan registers, frame cells and trap steps, in continuation form: each an evt
    from its entry pc whose exits hand an arbitrary continuation Q what holds there. Each statement quantifies the
    whole register file, the FP state and the memory; registers a piece leaves alone appear unchanged in its exit
    states. Statement text only: no function of a binary is proved here.
    - [near_stmt] 0x145ec -> 0x146f4 / 0x144f4: the inlined pod_nearest(f, 0, 255) of cell_value (pod.h:152-171,
      fuzz_headamp.c:105) with its six soft-float calls and four sanitizer checks (the float-cast checks
      `flt.s fs0 < fs3` 0x14624 and __gttf2(d, C2) 0x1463c; t + 1 0x146c0, t - 1 0x14694); f = the binary32 word at
      the start of the body of the entry e at pp + OFF_ENT + 104 v (a7 = &pp->ent[0].body, s7 = 104 v); result
      Pod/Nearest.v [nearest] f 0 255: Some n leaves n in s7 and goes to 0x146f4 (the value <= top test), None goes
      to the refusal fold 0x144f4 with a5 = OUT_OF_RANGE.
    - [key_stmt] 0x14354 -> 0x144f4 / 0x146fc: one pair whose key k has the prefix (strncmp returned 0): keys++,
      read_channel on rest = k + 13, the '.' test, the strcmp chain, the range, &ent[v], cell_value (pod_bool /
      pod_int / pod_float and [near_stmt]'s piece), value <= top; Pod/Headamp.v [expect_cell] k e: inl bad reaches
      the refusal fold 0x144f4 with a5 = bad, inr (ch, p, value) reaches the cap test 0x146fc with s9 = ch, a4 = p,
      s7 = value; both with n (s9 at entry) in the cell sp + 0x40 and the loop's registers reloaded.
    - [expect_stmt] 0x14198 -> 0x14784: expect_of (fuzz_headamp.c:109-157) inlined: memset(x), the NULL flag,
      is_props, params_struct, the constants, the pair loop with the pod_next_pair scan, and the store of x->rc
      (0x14780); at 0x14784 x (struct expect at sp + 0xb8) holds the bytes of Pod/Headamp.v [expect_model]
      (nl = 1) cap r. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The frame cells and FP registers of expect_of (UBSan 0x141e4-0x14264) *)
(** The binary32 words fs1 = -1.0f, fs2 = 256.0f (`lui; fmv.w.x`, 0x141e4 / 0x14200, 0x141e8 / 0x14204), the bounds
    of pod_nearest's range test d < lo - 1 || d > hi + 1 at lo = 0, hi = 255 made in binary32, and fs3 = 2^63
    (0x141ec / 0x14208), the bound of the float-cast check f < 2^63. *)
Definition F32_M1 : Z := 0xbf800000.
Definition F32_256 : Z := 0x43800000.
Definition F32_2P63 : Z := 0x5f000000.
(** The high words of 0.5L and -0.5L (low words 0) at sp + 0x50 and sp + 0x48 (0x14238, 0x14240). *)
Definition HALF_HI : Z := 0x3ffe000000000000.
Definition MHALF_HI : Z := 0xbffe000000000000.
(** C2 = -2^63 - 1 in binary128, the float-cast check's lower bound: low word at sp + 0x60 (0x14228), high word at
    sp + 0x58 (0x14230). *)
Definition C2_LO : Z := 0x0002000000000000.
Definition C2_HI : Z := 0xc03e000000000000.
(** read_channel's bound 1000000 at sp + 0x88 (0x14220). *)
Definition RC_BIG : Z := 1000000.

(** The stack the inlined pod_nearest's callees use below the harness sp: __subtf3 tail-calls __addtf3, whose frame
    is the 48 bytes below sp (CJ/RL/G/G_subtf3.v); the other five calls use none. *)
Definition NEAR_STACK : Z := 48.

(** The frame cells the nearest piece writes: the soft-float stack, and [sp + 0x28, sp + 0x40) (the saved param,
    d and frac). *)
Definition NEAR_W (sp : Z) : list ivl := [(sp - NEAR_STACK, sp); (sp + 0x28, sp + 0x40)].

(** ** 0x145ec -> 0x146f4 / 0x144f4: the inlined pod_nearest(f, 0, 255)
    Entry (pod_float passed: type Float, size >= 4, 0x145d0-0x145dc): a7 = &pp->ent[0].body, s7 = 104 v, the entry e
    at pp + OFF_ENT + 104 v with a body of at least 4 bytes; a4 = param; fs1 / fs2 / fs3 the three binary32 bounds;
    C2, 0.5L and -0.5L's words in the frame; the cells sp + 0x68, 0x98, 0xa0, 0xa8, 0xb0 the loop's saved
    registers, which both exits reload. In order: param to sp + 0x28; flw fs0; feq.s (NaN: None); d =
    __extendsftf2(f) to sp + 0x38 / 0x30; f < -1.0f or 256.0f < f (None); f < 2^63 (trap 0x14624 not taken);
    __gttf2(d, C2) > 0 (trap 0x1463c not taken); t = fcvt.l.s rtz f (s7); __floatditf(t); frac = __subtf3(d, .)
    (low word to sp + 0x38, high word in s10); __getf2(frac, 0.5L) >= 0: r = t + 1 (trap 0x146c0 not taken);
    __lttf2(frac, -0.5L) < 0: r = t - 1 (trap 0x14694 not taken); the reloads; 255 < r unsigned (None). It writes
    the 48 bytes below sp (__addtf3) and the cells [sp + 0x28, sp + 0x40); fs0 = f and fa0 (f8, f10), every other FP
    register as at entry; it accrues fflags with frm kept 0. *)
Definition near_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo pp : Z) (v : nat) (e : ent)
         (w68 w98 wa0 wa8 wb0 : word),
    a7 = Z_to_bv 64 (pp + OFF_ENT + 8) -> s7 = Z_to_bv 64 (ENT_SIZE * Z.of_nat v) -> (v < 32)%nat ->
    0 <= pp -> pp + POD_PROPS <= lo ->
    bytes_at rsegs m (pp + OFF_ENT + ENT_SIZE * Z.of_nat v) (ent_mem e) -> (4 <= length (e_body e))%nat ->
    Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1) ->
    Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256) ->
    Sem.reg_get F (Z_to_bv 5 19) = Sem.nan_box (Z_to_bv 32 F32_2P63) ->
    bytes_at rsegs m (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 MHALF_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 HALF_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 C2_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x60) (le8 (Z_to_bv 64 C2_LO)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 w68) ->
    bytes_at rsegs m (bv_unsigned sp + 0x98) (le8 w98) ->
    bytes_at rsegs m (bv_unsigned sp + 0xa0) (le8 wa0) ->
    bytes_at rsegs m (bv_unsigned sp + 0xa8) (le8 wa8) ->
    bytes_at rsegs m (bv_unsigned sp + 0xb0) (le8 wb0) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    (forall (t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte),
       frm0 fc' ->
       (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
       munch (NEAR_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       match nearest (rd32 (e_body e)) 0 255 with
       | Some n =>
           evt rsegs Q
             (MS (mkR wa8 sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 255) a1' w68 (Z_to_bv 64 9) a4 (Z_to_bv 64 5) w98 wa0
                      s2 s3 s4 s5 s6 (Z_to_bv 64 n) s8 s9 s10' s11 t3' t4' (Z_to_bv 64 8) wb0)
                 F' (Z_to_bv 64 0x146f4) fc' None m' (seg_rom rsegs))
       | None =>
           evt rsegs Q
             (MS (mkR wa8 sp gp tp t0' t1' t2' s0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 5) w98 wa0
                      s2 s3 s4 s5 s6 s7' s8 s9 s10' s11 t3' t4' (Z_to_bv 64 8) wb0)
                 F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs))
       end) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x145ec) fc None m (seg_rom rsegs)).

(** The frame cells the key piece writes: the soft-float stack, the param / d / frac / big / n cells
    [sp + 0x28, sp + 0x48), and x->keys at sp + 0x138. *)
Definition KEY_W (sp : Z) : list ivl := [(sp - NEAR_STACK, sp); (sp + 0x28, sp + 0x48); (sp + 0x138, sp + 0x13c)].

(** ** 0x14354 -> 0x144f4 / 0x146fc: one pair with the prefix
    Entry (0x14334 `beqz a0` took the strncmp = 0 branch): s11 = K, the key k NUL-terminated at K with the prefix;
    s9 = n (saved to sp + 0x40 at once, reloaded by the fold at 0x14500); s10 = v, s7 = 104 v, v the index of the
    pair's value e, an entry of the pp block at pp + OFF_ENT + 104 v; s8 = &pp->ent[0] and s0 = ~s8 (the &ent[v]
    pointer check); the frame cells sp + 0x88 = 1000000, sp + 0xa0 = &pp->ent[0].body, sp + 0x68, 0x98, 0xa8, 0xb0
    the loop's saved registers, x->keys at sp + 0x138; fs1 / fs2 / fs3 and C2 / 0.5L / -0.5L's words for the nearest
    piece. In order: x->keys++ (0x14358-0x14370, trap 0x1436c not taken); read_channel(rest = K + 13)
    (0x14374-0x1444c: the k + 13 check 0x1438c, the blanks loop 0x1439c, the sign, the digits loop 0x143f4 with the
    acc > 1000000 'big' rule and the acc * 10 check 0x1441c); `rest[used] == '.'` (0x14460, the rest + used checks
    0x14458 / 0x14464 / 0x14474); strcmp of name = rest + used + 1 against "phantom", "pad", "sens" (0x1448c,
    0x144a0, 0x144b4); big / ch > 47 (0x14548 / 0x14550); &ent[v] (0x14558 / 0x1455c not taken); cell_value:
    pod_bool (0x14584), pod_int (0x145a8, 0 <= i < 256), pod_float (0x145d0) and the nearest piece (0x145ec); value
    <= top (0x146f8). The refusals reach 0x144f4 with a5 = BAD_KEY 4 or OUT_OF_RANGE 5, a cell reaches 0x146fc;
    both with a2, a6, a7, t5, t6, ra reloaded. *)
Definition key_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo pp K keys : Z) (k : list byte) (v : nat)
         (e : ent) (w68 w98 wa8 wb0 : word),
    s11 = Z_to_bv 64 K -> bytes_at rsegs m K (k ++ [NUL]) -> ~ In NUL k -> ha_prefix k = true ->
    0 < K -> K + Z.of_nat (length k) + 1 <= lo ->
    s8 = Z_to_bv 64 (pp + OFF_ENT) -> s0 = Z_to_bv 64 (2^64 - 1 - (pp + OFF_ENT)) ->
    s10 = Z_to_bv 64 (Z.of_nat v) -> s7 = Z_to_bv 64 (ENT_SIZE * Z.of_nat v) -> (v < 32)%nat ->
    bytes_at rsegs m (pp + OFF_ENT + ENT_SIZE * Z.of_nat v) (ent_mem e) -> ent_wf e ->
    0 <= pp -> pp + POD_PROPS <= lo ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 w68) ->
    bytes_at rsegs m (bv_unsigned sp + 0x88) (le8 (Z_to_bv 64 RC_BIG)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x98) (le8 w98) ->
    bytes_at rsegs m (bv_unsigned sp + 0xa0) (le8 (Z_to_bv 64 (pp + OFF_ENT + 8))) ->
    bytes_at rsegs m (bv_unsigned sp + 0xa8) (le8 wa8) ->
    bytes_at rsegs m (bv_unsigned sp + 0xb0) (le8 wb0) ->
    bytes_at rsegs m (bv_unsigned sp + 0x138) (le4 (Z_to_bv 64 keys)) -> 0 <= keys < 2^31 - 1 ->
    Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1) ->
    Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256) ->
    Sem.reg_get F (Z_to_bv 5 19) = Sem.nan_box (Z_to_bv 32 F32_2P63) ->
    bytes_at rsegs m (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 MHALF_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 HALF_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 C2_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x60) (le8 (Z_to_bv 64 C2_LO)) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    (forall (t0' t1' t2' a0' a1' a3' a4' s7' s9' s10' s11' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte) (bad : Z),
       expect_cell k e = inl bad ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (KEY_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x138) (le4 (Z_to_bv 64 (keys + 1))) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x40) (le8 s9) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' s0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 bad) w98
                  (Z_to_bv 64 (pp + OFF_ENT + 8)) s2 s3 s4 s5 s6 s7' s8 s9' s10' s11' t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs))) ->
    (forall (t0' t1' t2' a0' a1' a5' s10' s11' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte) (ch p val : Z),
       expect_cell k e = inr (ch, p, val) ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (KEY_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x138) (le4 (Z_to_bv 64 (keys + 1))) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x40) (le8 s9) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' s0 s1 a0' a1' w68 (Z_to_bv 64 9) (Z_to_bv 64 p) a5' w98
                  (Z_to_bv 64 (pp + OFF_ENT + 8)) s2 s3 s4 s5 s6 (Z_to_bv 64 val) s8 (Z_to_bv 64 ch) s10' s11'
                  t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x146fc) fc' None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14354) fc None m (seg_rom rsegs)).

(** The frame cells expect_of writes: the soft-float stack below sp, its temporaries [sp + 0x28, sp + 0x68) (param,
    d / frac, n, -0.5L / 0.5L's high words, C2's words), and [sp + 0x80, sp + 0x140) (~&x->cell[0], 1000000, at, the
    saved loop registers, and x). The cells sp + 0x68 = &pp->n_ent, sp + 0x70 = pp and sp + 0x78 = &pp->len are
    read, never written. *)
Definition EXPECT_W (sp : Z) : list ivl :=
  [(sp - NEAR_STACK, sp); (sp + 0x28, sp + 0x68); (sp + 0x80, sp + 0x140)].

(** ** 0x14198 -> 0x14784: expect_of(pp, null, cap, &x) inlined, and x->rc
    Entry (pp->corrupt = 0: 0x14194 `bnez a0` not taken): s2 = cap, s8 = 1 - nl (the NULL flag's complement, from
    the cell sp + 0x10), s7 = &pp->len; the frame cells sp + 0x68 = &pp->n_ent, sp + 0x70 = pp, sp + 0x78 =
    &pp->len; the record r's pp_bytes at pp. In order: memset(x = sp + 0xb8, 0, 0x88) (0x141a4); s9 := (uint32)-1;
    `beqz s8` (0x141b0): nl = 1 goes to 0x14780; is_props (0x141b4) and params_struct (0x141bc) through s7 (rc -1,
    resp. 0 through 0x1477c); the constants (0x141c4-0x14264); the pair loop (head 0x14268, latch 0x1450c) with the
    n_ent test and the pod_next_pair scan (0x14294-0x142fc, its traps 0x14298 / 0x1429c / 0x142c0 / 0x14304 not
    taken), strncmp(k, "reac.headamp.", 13) (0x14330), [key_stmt]'s piece, the refusal fold (0x144f4-0x144fc), the
    cap break (0x14704 -> 0x148a4 -> 0x14780) and the cell write and n++ (0x14708-0x14760, its traps 0x14708 /
    0x14720 / 0x14734 / 0x14748 not taken); x->rc := s9 (0x14780). At 0x14784, x = the bytes of expect_model
    (nl = 1) cap r. *)
Definition expect_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : pod_rec) (nl cap pp lo : Z),
    pod_rec_wf r -> 0 <= nl <= 1 -> 0 <= cap <= 9 ->
    s2 = Z_to_bv 64 cap -> s8 = Z_to_bv 64 (1 - nl) -> s7 = Z_to_bv 64 (pp + POD_LEN_OFF) ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m pp (pp_bytes r) -> 0 <= pp -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    (forall (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
            (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
       frm0 fc' ->
       munch (EXPECT_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       bytes_at rsegs m' (bv_unsigned sp + 0xb8) (x_bytes (expect_model (nl =? 1) cap r)) ->
       evt rsegs Q
         (MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7' s8' s9' s10' s11'
                  t3' t4' t5' t6')
             F' (Z_to_bv 64 0x14784) fc' None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14198) fc None m (seg_rom rsegs)).

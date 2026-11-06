(** The internal statements of the checking segment's walk (plain LLVMFuzzerTestOneInput, segment M03 of
    Prog/LLVMFuzzerTestOneInput_c.v's headamp_check_contract, [0x14080, 0x14164)): three pieces in continuation form,
    each an evt from its entry pc whose exits hand an arbitrary continuation Q what holds there. Each statement
    quantifies the whole register file, the FP state and the memory; registers a piece leaves alone appear unchanged
    in its exit states. Statement text only: no function of a binary is proved here.
    - [near_stmt] 0x14548 -> 0x145e8 / 0x1464c: the inlined pod_nearest(f, 0, 255) of cell_value (pod.h:152-171,
      fuzz_headamp.c:105) with its five soft-float calls; f = the binary32 word at the start of the entry body;
      result Pod/Nearest.v [nearest] f 0 255: Some n stores n at sp + 0x40 and goes to 0x145e8 (value <= top),
      None goes to 0x1464c (the refusal OUT_OF_RANGE).
    - [key_stmt] 0x1433c -> 0x1465c / 0x14600: one pair whose key k has the prefix (strncmp returned 0): keys++,
      read_channel on rest = k + 13, the '.' test, the strcmp chain, the range, cell_value (pod_bool / pod_int /
      pod_float and [near_stmt]'s piece), value <= top; Pod/Headamp.v [expect_cell] k e: inl bad reaches the
      refusal fold 0x1465c with t3 = bad, inr (ch, p, value) reaches the cap test 0x14600 with s9 = ch, sp + 0x48 = p
      and sp + 0x40 = value.
    - [expect_stmt] 0x140f0 -> 0x14108: expect_of (fuzz_headamp.c:109-157) inlined: memset(x), the NULL flag,
      is_props, params_struct, n_ent, the constants, the pair loop with the pod_next_pair scan; at 0x14108 s0 is
      x->rc of Pod/Headamp.v [expect_model] (nl = 1) cap r and x's bytes past x->rc are its [x_tail]. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The frame cells of expect_of (plain 0x14244-0x142b0) *)
(** The binary32 words fs1 = -1.0f and fs2 = 256.0f (`lui; fmv.w.x`, 0x14260 / 0x14264, 0x14270 / 0x14290), the
    bounds of pod_nearest's range test d < lo - 1 || d > hi + 1 at lo = 0, hi = 255, made in binary32. *)
Definition F32_M1 : Z := 0xbf800000.
Definition F32_256 : Z := 0x43800000.
(** The high words of 0.5L and -0.5L (low words 0) at sp + 0x60 and sp + 0x50 (0x14298, 0x142a0). *)
Definition HALF_HI : Z := 0x3ffe000000000000.
Definition MHALF_HI : Z := 0xbffe000000000000.
(** read_channel's bound 1000000 at sp + 0x70 (0x1428c) and the prefix's address at sp + 0x88 (0x14284). *)
Definition RC_BIG : Z := 1000000.
Definition PREFIX_AT : Z := 0x102bd.

(** The stack the inlined pod_nearest's callees use below the harness sp: __subtf3 tail-calls __addtf3, whose frame
    is the 48 bytes below sp (CJ/RL/G/G_subtf3.v); the other four use none. *)
Definition NEAR_STACK : Z := 48.

(** The part of x (struct expect, at sp + 0x90) after x->rc: the cells, the zero cells up to ten, n, keys, refusal. *)
Definition x_tail (o : answer) : list byte :=
  x_cells_bytes (ans_cells o) ++ repeat (Z_to_bv 8 0) (12 * (X_CELLS - length (ans_cells o)))%nat ++ ans_res_bytes o.

Lemma x_bytes_tail : forall o, x_bytes o = le4 (Z_to_bv 64 (ans_rc o)) ++ x_tail o.
Proof. reflexivity. Qed.

(** ** 0x14548 -> 0x145e8 / 0x1464c: the inlined pod_nearest(f, 0, 255)
    Entry: a0 = &pp->ent[v], whose entry e has a body of at least 4 bytes (pod_float passed: type Float, size >= 4,
    0x14538-0x14544); fs1 / fs2 the two binary32 bounds; the 0.5L / -0.5L high words in the frame. It writes the
    48 bytes below sp (__addtf3) and the frame's d / frac / t / r cells [sp + 0x30, sp + 0x48); fs0 = f and fa0
    (f8, f10), every other FP register as at entry; it accrues fflags with frm kept 0. *)
Definition near_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (e : ent),
    bytes_at rsegs m (bv_unsigned a0) (ent_mem e) -> (4 <= length (e_body e))%nat ->
    Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1) ->
    Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256) ->
    bytes_at rsegs m (bv_unsigned sp + 0x60) (le8 (Z_to_bv 64 HALF_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 MHALF_HI)) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte),
       frm0 fc' ->
       (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
       munch [(bv_unsigned sp - NEAR_STACK, bv_unsigned sp); (bv_unsigned sp + 0x30, bv_unsigned sp + 0x48)] m m' ->
       wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       match nearest (rd32 (e_body e)) 0 255 with
       | Some n =>
           bytes_at rsegs m' (bv_unsigned sp + 0x40) (le8 (Z_to_bv 64 n)) ->
           evt rsegs Q
             (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x145e8) fc' None m' (seg_rom rsegs))
       | None =>
           evt rsegs Q
             (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x1464c) fc' None m' (seg_rom rsegs))
       end) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14548) fc None m (seg_rom rsegs)).

(** The frame cells the key piece writes: the soft-float stack, the d / frac / t / r / big / v / param / value cells
    [sp + 0x30, sp + 0x50), and x->keys at sp + 0x110. *)
Definition KEY_W (sp : Z) : list ivl := [(sp - NEAR_STACK, sp); (sp + 0x30, sp + 0x50); (sp + 0x110, sp + 0x114)].

(** ** 0x1433c -> 0x1465c / 0x14600: one pair with the prefix
    Entry (just after 0x14328 `beqz a0` took the strncmp = 0 branch): a0 = 0; s10 = K, the key k NUL-terminated at
    K with the prefix; s9 = v - 1, v the index of the pair's value e, an entry of the pp block at
    pp + OFF_ENT + 104 v; the frame cells sp + 0x68 = &pp->ent[0], sp + 0x70 = 1000000, sp + 0x80 = n_ent,
    x->keys at sp + 0x110; fs1 / fs2 and the 0.5L / -0.5L cells for the nearest piece. In order: x->keys++
    (0x1433c-0x14348); read_channel(rest = K + 13) (0x1434c-0x14410: the blanks loop 0x1436c, the sign, the digits
    loop 0x143d8 with the acc > 1000000 'big' rule); `rest[used] == '.'` (0x1441c); strcmp of name = rest + used + 1
    against "phantom", "pad", "sens" (0x1443c, 0x14450, 0x14464); big / ch > 47 (0x144b4-0x144bc); &ent[v]
    (0x144c0-0x144d4); cell_value: pod_bool (0x144f4), pod_int (0x14514, 0 <= i < 256), pod_float (0x14538) and the
    nearest piece (0x14548); value <= top (0x145fc). The refusals reach 0x1465c with t3 = BAD_KEY 4 or
    OUT_OF_RANGE 5 and t0 = n_ent, t1 = 104, t2 = 8 reloaded; a cell reaches 0x14600. *)
Definition key_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo pp K nent keys : Z) (k : list byte) (v : nat)
         (e : ent),
    a0 = Z_to_bv 64 0 ->
    s10 = Z_to_bv 64 K -> bytes_at rsegs m K (k ++ [NUL]) -> ~ In NUL k -> ha_prefix k = true ->
    0 < K -> K + Z.of_nat (length k) + 1 <= lo ->
    s9 = Z_to_bv 64 (Z.of_nat v - 1) -> (1 <= v < 32)%nat ->
    bytes_at rsegs m (pp + OFF_ENT + ENT_SIZE * Z.of_nat v) (ent_mem e) -> ent_wf e ->
    0 <= pp -> pp + POD_PROPS <= lo ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 (pp + OFF_ENT))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 RC_BIG)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 nent)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x110) (le4 (Z_to_bv 64 keys)) -> 0 <= keys < 2^31 - 1 ->
    Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1) ->
    Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256) ->
    bytes_at rsegs m (bv_unsigned sp + 0x60) (le8 (Z_to_bv 64 HALF_HI)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 MHALF_HI)) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    (forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s9' s10' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte) (bad : Z),
       expect_cell k e = inl bad ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (KEY_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x110) (le4 (Z_to_bv 64 (keys + 1))) ->
       evt rsegs Q
         (MS (mkR ra' sp gp tp (Z_to_bv 64 nent) (Z_to_bv 64 104) (Z_to_bv 64 8) s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9' s10' s11 (Z_to_bv 64 bad) t4' t5' t6')
             F' (Z_to_bv 64 0x1465c) fc' None m' (seg_rom rsegs))) ->
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
            (fc' : bv 32) (m' : word -> option byte) (ch p val : Z),
       expect_cell k e = inr (ch, p, val) ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (KEY_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x110) (le4 (Z_to_bv 64 (keys + 1))) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x40) (le8 (Z_to_bv 64 val)) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 p)) ->
       evt rsegs Q
         (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 ch) s10' s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x14600) fc' None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1433c) fc None m (seg_rom rsegs)).

(** The frame cells expect_of writes: the soft-float stack below sp, its temporaries [sp + 0x30, sp + 0x58)
    (d, frac, t / r / big, v / param, and -0.5L's high word over the cell that held &pp->len), and
    [sp + 0x60, sp + 0x118) (0.5L's high word, &ent[0], 1000000, the saved &ent[0].body and n_ent, the prefix's
    address, and x). The cell sp + 0x58 = pp is read, never written. *)
Definition EXPECT_W (sp : Z) : list ivl :=
  [(sp - NEAR_STACK, sp); (sp + 0x30, sp + 0x58); (sp + 0x60, sp + 0x118)].

(** ** 0x140f0 -> 0x14108: expect_of(pp, null, cap, &x) inlined
    Entry (pp->corrupt = 0: 0x140ec `bnez a0` not taken): s2 = cap, s7 = nl (the NULL flag), s8 = pp + 0x4d14; the
    frame cells sp + 0x50 = &pp->len, sp + 0x58 = pp; the record r's pp_bytes at pp. In order: memset(x = sp + 0x90,
    0, 0x88) (0x140fc); s0 := -1; `beqz s7` (0x14104): nl = 1 goes to 0x14108; is_props (0x14224) and params_struct
    (0x1422c) through sp + 0x50 (rc -1, resp. 0 through 0x14674); n_ent (0x14234, <= 0 gives 0); the constants
    (0x1423c-0x142b0); the pair loop (head 0x142b4, latch 0x14670) with the pod_next_pair scan (0x142c4-0x14308),
    strncmp(k, "reac.headamp.", 13) (0x14324), [key_stmt]'s piece, the refusal fold (0x1465c-0x14664), the cap break
    (0x14600 `bge s0,s2`) and the cell write and n++ (0x14604-0x14648). At 0x14108 (before `sw s0,0x90(sp)`, the
    store of x->rc): s0 = x->rc and x past x->rc = [x_tail] of expect_model (nl = 1) cap r. *)
Definition expect_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : pod_rec) (nl cap pp lo : Z),
    pod_rec_wf r -> 0 <= nl <= 1 -> 0 <= cap <= 9 ->
    s2 = Z_to_bv 64 cap -> s7 = Z_to_bv 64 nl -> s8 = Z_to_bv 64 (pp + POD_NENT_OFF) ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m pp (pp_bytes r) -> 0 <= pp -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + NEAR_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
            (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
       frm0 fc' ->
       munch (EXPECT_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       bytes_at rsegs m' (bv_unsigned sp + 0x94) (x_tail (expect_model (nl =? 1) cap r)) ->
       evt rsegs Q
         (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (ans_rc (expect_model (nl =? 1) cap r))) s1
                  a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7' s8' s9' s10' s11' t3' t4' t5' t6')
             F' (Z_to_bv 64 0x14108) fc' None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140f0) fc None m (seg_rom rsegs)).

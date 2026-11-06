(** Two sub-pieces of U/Prog/HeadCheck/Cut.v's [key_stmt] (UBSan LLVMFuzzerTestOneInput, one pair with the
    prefix), in the same continuation form: each an evt from its entry pc whose exits hand an arbitrary continuation
    Q what holds there; registers a piece leaves alone appear unchanged in its exit states. Statement text only: no
    function of a binary is proved here.
    - [rc_stmt] 0x14374 -> 0x14438: read_channel(rest = K + 13) (fuzz_headamp.c:67-85) up to the first byte after
      the digits: the k + 13 check (trap 0x1438c not taken), the blanks loop 0x1439c (trap 0x143b4 not taken), the
      sign 0x143b8-0x143dc, the check 0x143e0 (trap not taken), the digits loop 0x143f4 with the acc > 1000000 'big'
      rule and the acc * 10 check 0x1441c (traps 0x1441c / 0x14434 not taken). At 0x14438: a1 = the blanks and the
      sign read (d), a4 = the digits read, s9 = acc, t4 = big, a3 = 0 after a '-' else 1, a6 = K + d + digits, a7 =
      the byte after the digits; Pod/Headamp.v [rc_blanks], [rc_sign], [rc_digits] on rest. It writes no memory.
    - [val_stmt] 0x14554 -> 0x144f4 / 0x146fc: the &ent[v] checks (traps 0x14558 / 0x1455c not taken) and
      cell_value(ent[v]) (fuzz_headamp.c:94-107: pod_bool 0x14584, pod_int 0x145a8 with 0 <= i < 256, pod_float
      0x145d0 and the inlined pod_nearest from 0x145ec, U/Prog/HeadCheck/Cut.v's [near_stmt]), then value <= top
      (0x146f4 / 0x146f8) with top = [ktop] p in s11: Pod/Headamp.v [cell_value] e out of [0, top] reaches the
      refusal fold 0x144f4 with a5 = OUT_OF_RANGE 5, else the cap test 0x146fc with s7 = the value. It writes only
      what the nearest piece writes ([NEAR_W]). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import KeyFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut.
Import ListNotations.
Open Scope Z_scope.

(** ** 0x14374 -> 0x14438: read_channel on rest = K + 13 up to the byte after the digits
    Entry (after keys++): s11 = K, the key k NUL-terminated at K, at least 13 bytes long (the prefix); the cell
    sp + 0x88 = 1000000. In order: a0 = -13, a5 = 5, a6 = 0x20, t1 = 9, t2 = 10, t3 = 1000000 (`ld 0x88(sp)`);
    `bgeu s11, a0` (k + 13 wraps; not taken); a1 = 0, a0 = rest, a2 = ~rest; the blanks loop (bytes 9..13 and 32;
    `bgeu a2, a1` back, else the trap); the sign ('+' / '-': a1 += 1, a3 = (c != '-'); else a3 = 1); `bltu a2, a1`
    (trap; not taken); a4 = t4 = s9 = 0, a5 = K + d; the digits loop (a7 = rest[d + a4]; `bltu t1, a7 - 0x30` ends
    it; acc > 1000000 sets t4 = 1, else acc = acc * 10 + digit after the mulh / mul check; a4 += 1; `bgeu a2, a1 + a4`
    back, else the trap). The exit leaves t0 and a5 unnamed. *)
Definition rc_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (K : Z) (k : list byte),
    s11 = Z_to_bv 64 K -> bytes_at rsegs m K (k ++ [NUL]) -> ~ In NUL k -> (13 <= length k)%nat ->
    0 < K -> K + Z.of_nat (length k) + 1 < 2^64 ->
    bytes_at rsegs m (bv_unsigned sp + 0x88) (le8 (Z_to_bv 64 RC_BIG)) ->
    (forall (t0' a5' : word) (neg : bool) (sn nd : nat) (acc : Z) (big : bool),
       rc_sign (skipn (rc_blanks (skipn 13 k)) (skipn 13 k)) = (neg, sn) ->
       rc_digits 0 false (skipn (rc_blanks (skipn 13 k) + sn) (skipn 13 k)) = (acc, big, nd) ->
       0 <= acc <= 10000009 -> (rc_blanks (skipn 13 k) + sn + nd <= length (skipn 13 k))%nat ->
       evt rsegs Q
         (MS (mkR ra sp gp tp t0' (Z_to_bv 64 9) (Z_to_bv 64 10) s0 s1 (Z_to_bv 64 (K + 13))
                  (Z_to_bv 64 (Z.of_nat (rc_blanks (skipn 13 k) + sn))) (Z_to_bv 64 (2^64 - 1 - (K + 13)))
                  (Z_to_bv 64 (if neg then 0 else 1)) (Z_to_bv 64 (Z.of_nat nd)) a5'
                  (Z_to_bv 64 (K + Z.of_nat (rc_blanks (skipn 13 k) + sn + nd)))
                  (zxb (nth (rc_blanks (skipn 13 k) + sn + nd) (skipn 13 k) NUL))
                  s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 acc) s10 s11 (Z_to_bv 64 RC_BIG)
                  (Z_to_bv 64 (if big then 1 else 0)) t5 t6)
             F (Z_to_bv 64 0x14438) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14374) fc None m (seg_rom rsegs)).

(** ** 0x14554 -> 0x144f4 / 0x146fc: &ent[v], cell_value(ent[v]) and value <= top
    Entry (big = 0 and 0 <= ch < 48 passed, 0x14540-0x14550): a4 = p, s11 = [ktop] p, a3 = 9, a5 = OUT_OF_RANGE 5;
    ra, t5, t6 as reloaded (sp + 0xa8, 8, sp + 0xb0); s10 = v, s7 = 104 v, v < 32, the value e = ent[v] at
    pp + OFF_ENT + 104 v; s8 = &pp->ent[0] and s0 = ~s8; the frame cells and FP registers [near_stmt] reads. In
    order: `bgeu s10, 33` and `bltu s0, s7` (traps; not taken); the type at s8 + s7: 6 -> pod_float, 4 -> pod_int,
    2 -> pod_bool, else the refusal (0x145e0, a2 / a6 reloaded). pod_bool: size < 4 refuses, else s7 = (word != 0)
    and `j 0x146fc`; pod_int: size < 4 refuses, s7 = word, 256 <= s7 (unsigned) refuses, else `j 0x146f4`;
    pod_float: size < 4 refuses, else [near_stmt]'s piece from 0x145ec (Some n: 0x146f4 with s7 = n; None: the
    refusal). 0x146f4 `sext.w a0, s7; bltu s11, a0`: value > top refuses, else 0x146fc. Both exits carry a2, a6, a7,
    t5, t6, ra reloaded, s9 and s11 as at entry, F off f8 / f10, frm 0, and the memory changed only in [NEAR_W]. *)
Definition val_stmt : Prop :=
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo pp p : Z) (v : nat) (e : ent)
         (w68 w98 wa8 wb0 : word),
    a4 = Z_to_bv 64 p -> s11 = Z_to_bv 64 (ktop p) -> a3 = Z_to_bv 64 9 -> a5 = Z_to_bv 64 REFUSE_OUT_OF_RANGE ->
    ra = wa8 -> t5 = Z_to_bv 64 8 -> t6 = wb0 ->
    s8 = Z_to_bv 64 (pp + OFF_ENT) -> s0 = Z_to_bv 64 (2^64 - 1 - (pp + OFF_ENT)) ->
    s10 = Z_to_bv 64 (Z.of_nat v) -> s7 = Z_to_bv 64 (ENT_SIZE * Z.of_nat v) -> (v < 32)%nat ->
    bytes_at rsegs m (pp + OFF_ENT + ENT_SIZE * Z.of_nat v) (ent_mem e) -> ent_wf e ->
    0 <= pp -> pp + POD_PROPS <= lo ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 w68) ->
    bytes_at rsegs m (bv_unsigned sp + 0x98) (le8 w98) ->
    bytes_at rsegs m (bv_unsigned sp + 0xa0) (le8 (Z_to_bv 64 (pp + OFF_ENT + 8))) ->
    bytes_at rsegs m (bv_unsigned sp + 0xa8) (le8 wa8) ->
    bytes_at rsegs m (bv_unsigned sp + 0xb0) (le8 wb0) ->
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
    (forall (t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte),
       (cell_value e <? 0) || (ktop p <? cell_value e) = true ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (NEAR_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' s0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 REFUSE_OUT_OF_RANGE) w98
                  (Z_to_bv 64 (pp + OFF_ENT + 8)) s2 s3 s4 s5 s6 s7' s8 s9 s10' s11 t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs))) ->
    (forall (t0' t1' t2' a0' a1' a5' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte),
       (cell_value e <? 0) || (ktop p <? cell_value e) = false ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (NEAR_W (bv_unsigned sp)) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' s0 s1 a0' a1' w68 (Z_to_bv 64 9) (Z_to_bv 64 p) a5' w98
                  (Z_to_bv 64 (pp + OFF_ENT + 8)) s2 s3 s4 s5 s6 (Z_to_bv 64 (cell_value e)) s8 s9 s10' s11
                  t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x146fc) fc' None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14554) fc None m (seg_rom rsegs)).

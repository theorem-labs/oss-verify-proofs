(** The cuts of the walk of reac_headamp_prop_parse_result (plain image, 0x1487c, 254 instructions) against
    Prog/reac_headamp_prop_parse_result_c.v: the state at each cut and what each segment file proves of it. Statement
    text and the model steps every segment reads; no function of a binary is proved here.

    Segments (each file proves its statement from the statements of the cuts it
    reaches, so the files build apart and Prog/reac_headamp_prop_parse_result.v joins them):
      - Seg/ParseExit.v:  [S_EPI] (0x149b8: a0 = s1, the thirteen reloads, fs0, sp back, ret) and [S_EXIT] (0x149a0:
        res->n, res->keys, res->refusal when res <> 0, then the epilogue);
      - Seg/ParseValue.v: [S_REFUSE] (0x14c5c: the first refusal is kept, s8 reloaded, then the advance) and
        [S_VALUE] (0x14b5c: value_pod_to_byte with reac_float_nearest inlined, value_in_range, the n >= max break,
        out[n] = (ch, param, value), n++, then the advance);
      - Seg/ParseKey.v:   [S_KEY] (0x14ab4: keys++, strtol(key + 13, &dot, 10), the '.' test, strcmp against
        "phantom" / "pad" / "sens", the channel range, then [S_VALUE] or [S_REFUSE]);
      - Seg/ParseWalk.v:  [S_WALK] (0x14a28, SPA_POD_STRUCT_FOREACH: an induction on its fuel; the key slot by
        spa_pod_get_string, strncmp(key, "reac.headamp.", 13), then [S_KEY]; the advance at 0x14a94 is the
        continuation [K_ADV] it gives the key and value cuts; the walk's end is [S_EXIT]);
      - Seg/ParseEntry.v: [S_ENTRY] (0x1487c: the prologue, res zeroed, the NULL return, spa_pod_is_object_type, the
        find loop at 0x14938, spa_pod_is_struct, the walk setup, then [S_WALK]; every other exit is [S_EPI]).

    The call's fixed quantities are one record [pctx] (Prog/Seg/ParseModel.v, shared with the UBSan cuts, with the
    saved-register cells [saves], [fp_ok], the Struct and key-slot facts and the per-pair model steps): the caller's
    ra, sp, gp, tp and s0 .. s11, the memory at the call, and the contract's lo, P (the pod), O (out), cap, R (res),
    bs, ev, can. [pc_ok] is the contract's premise list on it (parse_args, the stack, no ROM in it, mem_inv). Every
    cut runs below the parse's frame at spf = sp - 0xa0, holding the seven temporary cells 0x00 .. 0x30 (0x08 the
    range bound, 0x10 the channel, 0x18 the prefix pointer 0x102bd, 0x20 the float temp, 0x28 strtol's end pointer
    dot, 0x30 fs0) and the saves s11 .. s0, ra at 0x38 .. 0x98. Inside the walk the FP state is any with fs0 = +0.0
    and rounding mode 0 ([fp_ok]). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa SpaBool Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Export ParseModel.
Import ListNotations.
Open Scope Z_scope.

(** ** The call *)
(** The contract's premises on the call (reac_headamp_prop_parse_result_contract but frm0, which each cut states of
    its own FP state). *)
Definition pc_ok (c : pctx) : Prop :=
  parse_args (c_m c) (c_lo c) (bv_unsigned (c_sp c)) (c_tp c) (c_P c) (c_O c) (c_cap c) (c_R c) (c_bs c)
    (c_ev c) (c_can c) /\
  stk rsegs (c_m c) (c_lo c) (bv_unsigned (c_sp c)) /\ c_lo c + PARSE_STACK <= bv_unsigned (c_sp c) /\
  (forall a, c_lo c <= a < bv_unsigned (c_sp c) -> seg_rom rsegs (wa a) = None) /\ mem_inv rsegs (c_m c).

(** The parse's sp (0x1487c `addi sp,sp,-0xa0`) and errno. *)
Definition c_spf (c : pctx) : Z := bv_unsigned (c_sp c) + -160.
Definition c_E (c : pctx) : Z := PARSE_ERRNO (c_tp c).

(** The contract's post for the answer o. *)
Definition PPost (c : pctx) (o : answer) : machine_state -> Prop :=
  parse_post (c_ra c) (c_sp c) (c_gp c) (c_tp c) (c_s0 c) (c_s1 c) (c_s2 c) (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c)
    (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) (c_m c) (c_lo c) (c_O c) (c_R c) o.

(** ** The frame and the memory at a cut *)
(** The frame inside the walk: the prefix pointer at 0x18 (0x14a24 `sd s8,0x18(sp)`, reloaded at 0x14c6c), the
    other temporary cells any bytes; the saved registers (ParseModel.saves) at 0x38 .. 0xa0 (0x148b0
    `sd s11,0x38(sp)` .. 0x14880 `sd ra,0x98(sp)`). *)
Definition wframe (c : pctx) (ja jb : list byte) : list Cells.cell :=
  CB 24 ja :: C8 (Z_to_bv 64 LIT_PREFIX) :: CB 24 jb :: saves c.

(** The frame at the value cut: the range bound at 0x08 (0x14b04 / 0x14b3c) and the channel at 0x10 (0x14ae8). *)
Definition vframe (c : pctx) (ja : list byte) (bound ch : word) (jb : list byte) : list Cells.cell :=
  CB 8 ja :: C8 bound :: C8 ch :: C8 (Z_to_bv 64 LIT_PREFIX) :: CB 24 jb :: saves c.

(** The memory at a cut with the frame fr and the cells cl written to out: the frame, the stack below it, every
    change since the call inside the parse's writes for n = |cl| (parse_writes), out[0, 3|cl|) = the cells, errno a
    cell, writable bytes kept, mem_inv. *)
Definition PMem (c : pctx) (fr : list Cells.cell) (cl : list Headamp.cell) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (c_spf c) fr /\
  stk rsegs m (c_lo c) (c_spf c) /\
  munch (parse_writes (bv_unsigned (c_sp c)) (c_O c) (Z.of_nat (length cl)) (c_E c) (c_R c)) (c_m c) m /\
  bytes_at rsegs m (c_O c) (ha_cells_bytes cl) /\
  (exists ev', rw_cells rsegs m (c_E c) [C4 ev']) /\
  wmono rsegs (c_m c) m /\ mem_inv rsegs m.

(** ** The cuts *)
(** [K_ADV c r cc rest]: the advance at 0x14a94 of the pass on the child cc (s6 = 0, s8 = the prefix pointer
    again), from any state (cl, keys, rf) whose fold over the pairs after this child, rest, is the answer. The walk
    shows it for each pass; the key, value and refusal cuts take it as their continuation. *)
Definition K_ADV (c : pctx) (r cc : Z) (rest : list (list byte * ent)) : Prop :=
  forall (cl : list Headamp.cell) (keys rf : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ja jb : list byte),
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc + 8 - (r + 16) -> 0 <= rf <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c) rest cl keys rf) = RESM c ->
    PMem c (wframe c ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               (Z_to_bv 64 0) (Z_to_bv 64 keys) (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14a94) fc None m (seg_rom rsegs)).

(** [S_EPI]: from 0x149b8 with s1 = the answer's rc, on a memory whose out holds its cells and whose res (when not
    NULL) holds its (n, keys, refusal): Post. The frame's temporary cells are one block of 56 bytes. *)
Definition S_EPI (c : pctx) : Prop :=
  forall (o : answer) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (ja : list byte),
    PMem c (CB 56 ja :: saves c) (ans_cells o) m ->
    (c_R c <> 0 -> bytes_at rsegs m (c_R c) (ans_res_bytes o)) ->
    frm0 fc ->
    evt rsegs (PPost c o)
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 x8 (Z_to_bv 64 (ans_rc o))
               x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x149b8) fc None m (seg_rom rsegs)).

(** [S_EXIT]: from 0x149a0 (the walk's end, the n >= max break) with s1 = |cl|, s7 = keys, s4 = rf and
    (cl, keys, rf) the folded answer: res->n, res->keys, res->refusal when res <> 0, then Post. *)
Definition S_EXIT (c : pctx) : Prop :=
  forall (cl : list Headamp.cell) (keys rf : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (ja : list byte),
    ha_result (cl, keys, rf) = RESM c ->
    PMem c (CB 56 ja :: saves c) cl m -> frm0 fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 rf) x21 x22
               (Z_to_bv 64 keys) x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x149a0) fc None m (seg_rom rsegs)).

(** [S_REFUSE]: from 0x14c5c with s8 = the refusal bad of the pair at cc (keys already counted: s7 = keys + 1):
    the first refusal is kept (0x14c5c-0x14c68), s8 reloaded (0x14c6c), then the advance. *)
Definition S_REFUSE (c : pctx) : Prop :=
  forall (r cc : Z) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf bad : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 -> 0 <= bad <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c) rest cl (keys + 1) (if rf =? REFUSE_NONE then bad else rf)) = RESM c ->
    PMem c (wframe c ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               x22 (Z_to_bv 64 (keys + 1)) (Z_to_bv 64 bad) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14c5c) fc None m (seg_rom rsegs)).

(** [S_VALUE]: from 0x14b5c, the key of the pair at cc read as the cell address (ch, p) (a0 = p, 0x08 = the range
    bound 2 or 0x38, 0x10 = ch; keys counted: s7 = keys + 1): value_pod_to_byte on the child at cc, value_in_range,
    the n >= max break to [S_EXIT], or out[n] = (ch, p, value) and n++, or the refusal OUT_OF_RANGE; then the advance. *)
Definition S_VALUE (c : pctx) : Prop :=
  forall (r cc ch p : Z) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x28 x29 x30 x31 : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    st_ok c r -> r + 16 <= cc -> cc mod 8 = 0 -> child_in c r cc ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    0 <= ch < REAC_HEADAMP_MAX_CH -> 0 <= p <= HA_SENS ->
    ha_result (fold_after (c_cap c) (vcell ch p (child_at (c_bs c) cc)) rest cl keys rf) = RESM c ->
    PMem c (vframe c ja (Z_to_bv 64 (if p =? HA_SENS then 0x38 else 2)) (Z_to_bv 64 ch) jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               x22 (Z_to_bv 64 (keys + 1)) x24 (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14b5c) fc None m (seg_rom rsegs)).

(** [S_KEY]: from 0x14ab4, the key string k at offset kk of the pod has the prefix (strncmp returned 0) and its value
    pod is the child at cc: keys++, parse_key through strtol and three strcmp, then [S_VALUE] or [S_REFUSE]. *)
Definition S_KEY (c : pctx) : Prop :=
  forall (r cc kk : Z) (k : list byte) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    st_ok c r -> r + 16 <= cc -> cc mod 8 = 0 -> child_in c r cc ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    key_ok c (Some kk) (Some k) -> ha_prefix k = true ->
    ha_result (fold_after (c_cap c) (parse_cell k (child_at (c_bs c) cc)) rest cl keys rf) = RESM c ->
    PMem c (wframe c ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               (Z_to_bv 64 (c_P c + kk)) (Z_to_bv 64 keys) (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14ab4) fc None m (seg_rom rsegs)).

(** [S_WALK]: the head of SPA_POD_STRUCT_FOREACH at 0x14a28 on the child at offset cc (s10 = P + cc; s9 = the
    Struct pod P + r + 8, s5 = its body P + r + 16, s11 = 8), the key slot k / km, n passes of fuel, the state
    (cl, keys, rf) whose fold over the pairs from cc on is the answer. *)
Definition S_WALK (c : pctx) : Prop :=
  forall (r : Z) (n : nat) (cc : Z) (k : option Z) (km : option (list byte)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ja jb : list byte),
    st_ok c r -> r + 16 <= cc <= r + 16 + u32_at (c_bs c) (r + 8) + 7 -> cc mod 8 = 0 ->
    (Z.to_nat (r + 16 + u32_at (c_bs c) (r + 8) - cc) < n)%nat ->
    key_ok c k km ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c) (walk_pairs (c_bs c) r cc n km) cl keys rf) = RESM c ->
    PMem c (wframe c ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               (key_reg c k) (Z_to_bv 64 keys) (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14a28) fc None m (seg_rom rsegs)).

(** [S_ENTRY]: the call at 0x1487c, props NULL (null) or the pod: Post for parse_props. *)
Definition S_ENTRY (c : pctx) : Prop :=
  forall (null : bool) (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    frm0 fc ->
    evt rsegs (PPost c (parse_props (parse_arg null (c_bs c)) (c_cap c)))
      (MS (mkR (c_ra c) (c_sp c) (c_gp c) (c_tp c) t0 t1 t2 (c_s0 c) (c_s1 c)
               (Z_to_bv 64 (if null then 0 else c_P c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 (c_cap c))
               (Z_to_bv 64 (c_R c)) a4 a5 a6 a7 (c_s2 c) (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c)
               (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
          F (Z_to_bv 64 HA_PARSE_RESULT) fc None (c_m c) (seg_rom rsegs)).

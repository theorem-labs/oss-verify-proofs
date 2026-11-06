(** The cuts of the walk of reac_headamp_prop_parse_result (UBSan image, 0x14cd0, 297 instructions, 17 trap
    branches to the `unimp` at 0x15170) against U/Prog/reac_headamp_prop_parse_result_c.v: the state at each cut and
    what each segment file proves of it. The plain cuts' plan (lib/Prog/Seg/ParseCut.v) with the UBSan code's
    registers, frame and addresses; Prog/Seg/ParseModel.v (exported) holds what both builds share. Statement text
    only; no function of a binary is proved here.

    Segments (each file proves its statement from the statements of the cuts it
    reaches, and U/Prog/reac_headamp_prop_parse_result.v joins them):
      - U/Prog/Seg/ParseExit.v:  [S_EPI] (0x15108: a0 = s1, the thirteen reloads, fs0, sp back, ret) and [S_EXIT]
        (0x15150: `beqz s0`, the res & 3 trap 0x15158, res->n = s1, res->keys = s5, res->refusal = the frame's 0x08);
      - U/Prog/Seg/ParseValue.v: [S_REFUSE] (0x150ec: the first refusal is kept in the frame's 0x08, then the advance
        at 0x14eb0) and [S_VALUE] (0x14f9c: value_pod_to_byte with reac_float_nearest inlined and its two cast traps
        0x150b4 / 0x150c4 and the r - 1 trap 0x150dc, value_in_range split on the phantom/pad flag a1, the n >= max
        break, the three out-pointer traps 0x15010 / 0x15024 / 0x15028, out[n] = (ch, param, value), n++);
      - U/Prog/Seg/ParseKey.v:   [S_KEY] (0x14ed4: keys + 1 into s5 with its overflow trap 0x14ed8, the key + 13 trap
        0x14ee0, strtol(key + 13, &dot, 10) with dot at 0x18(sp), the dot traps 0x14f08 / 0x14f20, the '.' test,
        strcmp against "phantom" / "pad" / "sens", the channel range);
      - U/Prog/Seg/ParseWalk.v:  [S_WALK] (0x14e18: the guards, the C = 0 trap 0x14e30, spa_pod_get_string with its
        two end-pointer traps 0x14e6c / 0x14e7c, strncmp(key, "reac.headamp.", 13), then [S_KEY]; the advance at
        0x14eb0 is [K_ADV]; the walk's end is 0x1514c `mv s5,s7` then [S_EXIT]);
      - U/Prog/Seg/ParseEntry.v: [S_ENTRY] (0x14cd0: the prologue, the res & 3 trap 0x14d20, res zeroed, the NULL
        return, the props & 3 trap 0x14d3c, spa_pod_is_object_type, the find loop at 0x14d94, the prop & 3 trap
        0x14dd4, spa_pod_is_struct, the walk setup, then [S_WALK]; every other exit is [S_EPI]).

    Registers inside the walk: s0 = res, s1 = n, s2 = cap, s3 = out, s4 = the prefix pointer 0x102bd, s5 = keys after
    this pair (set at 0x14eac / 0x14ed4, copied to s7 at 0x14ec8), s6 = the key slot, s7 = keys (and the refusal
    code from 0x14f00 on), s8 = the child C = P + cc, s9 = 8, s10 = the Struct pod V = P + r + 8, s11 = its body
    SB = P + r + 16. The frame at spf = sp - 0x90: 0x00 the channel (0x14f18 `sd a0,0(sp)`), 0x08 the refusal
    (0x14df4 `sd zero,8(sp)`, 0x150fc `sd s7,8(sp)`), 0x10 the float temp, 0x18 strtol's end pointer dot, 0x20 fs0,
    then the saves s11 .. s0, ra at 0x28 .. 0x90 (0x14d04 `sd s11,0x28(sp)` .. 0x14cd4 `sd ra,0x88(sp)`). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa SpaBool Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c ParseSites.
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

(** The parse's sp (0x14cd0 `addi sp,sp,-0x90`) and errno. *)
Definition c_spf (c : pctx) : Z := bv_unsigned (c_sp c) + -144.
Definition c_E (c : pctx) : Z := PARSE_ERRNO (c_tp c).

(** The contract's post for the answer o. *)
Definition PPost (c : pctx) (o : answer) : machine_state -> Prop :=
  parse_post (c_ra c) (c_sp c) (c_gp c) (c_tp c) (c_s0 c) (c_s1 c) (c_s2 c) (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c)
    (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) (c_m c) (c_lo c) (c_O c) (c_R c) o.

(** ** The frame and the memory at a cut *)
(** The frame inside the walk: the refusal rf at 0x08, the other temporary cells any bytes. *)
Definition wframe (c : pctx) (rf : Z) (ja jb : list byte) : list Cells.cell :=
  CB 8 ja :: C8 (Z_to_bv 64 rf) :: CB 24 jb :: saves c.

(** The frame at the value cut: the channel at 0x00 (0x14f18), the refusal at 0x08. *)
Definition vframe (c : pctx) (ch : word) (rf : Z) (jb : list byte) : list Cells.cell :=
  C8 ch :: C8 (Z_to_bv 64 rf) :: CB 24 jb :: saves c.

(** The memory at a cut with the frame fr and the cells cl written to out (as the plain file's). *)
Definition PMem (c : pctx) (fr : list Cells.cell) (cl : list Headamp.cell) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (c_spf c) fr /\
  stk rsegs m (c_lo c) (c_spf c) /\
  munch (parse_writes (bv_unsigned (c_sp c)) (c_O c) (Z.of_nat (length cl)) (c_E c) (c_R c)) (c_m c) m /\
  bytes_at rsegs m (c_O c) (ha_cells_bytes cl) /\
  (exists ev', rw_cells rsegs m (c_E c) [C4 ev']) /\
  wmono rsegs (c_m c) m /\ mem_inv rsegs m.

(** ** The cuts *)
(** [K_ADV c r cc rest]: the advance at 0x14eb0 of the pass on the child cc (s5 = keys, s6 = 0, the frame's 0x08 =
    rf), from any state (cl, keys, rf) whose fold over the pairs after this child, rest, is the answer. *)
Definition K_ADV (c : pctx) (r cc : Z) (rest : list (list byte * ent)) : Prop :=
  forall (cl : list Headamp.cell) (keys rf : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) (ja jb : list byte),
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc + 8 - (r + 16) -> 0 <= rf <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c) rest cl keys rf) = RESM c ->
    PMem c (wframe c rf ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 keys)
               (Z_to_bv 64 0) x23 (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + r + 16)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14eb0) fc None m (seg_rom rsegs)).

(** [S_EPI]: from 0x15108 with s1 = the answer's rc: Post. The frame's temporary cells are one block of 40 bytes. *)
Definition S_EPI (c : pctx) : Prop :=
  forall (o : answer) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (ja : list byte),
    PMem c (CB 40 ja :: saves c) (ans_cells o) m ->
    (c_R c <> 0 -> bytes_at rsegs m (c_R c) (ans_res_bytes o)) ->
    frm0 fc ->
    evt rsegs (PPost c o)
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 x8 (Z_to_bv 64 (ans_rc o))
               x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15108) fc None m (seg_rom rsegs)).

(** [S_EXIT]: from 0x15150 (the walk's end after 0x1514c `mv s5,s7`, the n >= max break, the advance's alignment
    exit) with s1 = |cl|, s5 = keys, the frame's 0x08 = rf and (cl, keys, rf) the folded answer: res->n, res->keys,
    res->refusal when res <> 0 (the res & 3 trap 0x15158 not taken), then Post. *)
Definition S_EXIT (c : pctx) : Prop :=
  forall (cl : list Headamp.cell) (keys rf : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (ja jb : list byte),
    ha_result (cl, keys, rf) = RESM c ->
    PMem c (wframe c rf ja jb) cl m -> frm0 fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 keys)
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15150) fc None m (seg_rom rsegs)).

(** [S_REFUSE]: from 0x150ec with s7 = the refusal bad of the pair at cc (keys counted: s5 = keys + 1): the first
    refusal is kept (0x150ec-0x150fc, stored back at 0x08), then the advance. *)
Definition S_REFUSE (c : pctx) : Prop :=
  forall (r cc : Z) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf bad : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 -> 0 <= bad <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c) rest cl (keys + 1) (if rf =? REFUSE_NONE then bad else rf)) = RESM c ->
    PMem c (wframe c rf ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 (keys + 1))
               x22 (Z_to_bv 64 bad) (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + r + 16)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x150ec) fc None m (seg_rom rsegs)).

(** [S_VALUE]: from 0x14f9c, the key of the pair at cc read as the cell address (ch, p): a0 = p, a1 = 1 for
    phantom / pad and 0 for sens (the range bound's selector, 0x14fc8), a4 = 4, a6 = ch, the frame's 0x00 = ch;
    keys counted (s5 = keys + 1): value_pod_to_byte on the child at cc, value_in_range, the n >= max break to
    [S_EXIT], or out[n] = (ch, p, value) and n++, or the refusal OUT_OF_RANGE; then the advance. *)
Definition S_VALUE (c : pctx) : Prop :=
  forall (r cc ch p : Z) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x12 x13 x15 x17 x22 x23 x28 x29 x30 x31 : word) (jb : list byte),
    K_ADV c r cc rest ->
    st_ok c r -> r + 16 <= cc -> cc mod 8 = 0 -> child_in c r cc ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    0 <= ch < REAC_HEADAMP_MAX_CH -> 0 <= p <= HA_SENS ->
    ha_result (fold_after (c_cap c) (vcell ch p (child_at (c_bs c) cc)) rest cl keys rf) = RESM c ->
    PMem c (vframe c (Z_to_bv 64 ch) rf jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) (Z_to_bv 64 p) (Z_to_bv 64 (if p =? HA_SENS then 0 else 1))
               x12 x13 (Z_to_bv 64 4) x15 (Z_to_bv 64 ch) x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 (keys + 1))
               x22 x23 (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + r + 16)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14f9c) fc None m (seg_rom rsegs)).

(** [S_KEY]: from 0x14ed4, the key string k at offset kk of the pod has the prefix (strncmp returned 0) and its value
    pod is the child at cc: keys + 1, parse_key through strtol and three strcmp, then [S_VALUE] or [S_REFUSE]. *)
Definition S_KEY (c : pctx) : Prop :=
  forall (r cc kk : Z) (k : list byte) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    st_ok c r -> r + 16 <= cc -> cc mod 8 = 0 -> child_in c r cc ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    key_ok c (Some kk) (Some k) -> ha_prefix k = true ->
    ha_result (fold_after (c_cap c) (parse_cell k (child_at (c_bs c) cc)) rest cl keys rf) = RESM c ->
    PMem c (wframe c rf ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 LIT_PREFIX) x21
               (Z_to_bv 64 (c_P c + kk)) (Z_to_bv 64 keys) (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8)
               (Z_to_bv 64 (c_P c + r + 8)) (Z_to_bv 64 (c_P c + r + 16)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14ed4) fc None m (seg_rom rsegs)).

(** [S_WALK]: the head of SPA_POD_STRUCT_FOREACH at 0x14e18 on the child at offset cc (s8 = P + cc; s10 = the
    Struct pod P + r + 8, s11 = its body P + r + 16, s9 = 8), the key slot k / km, n passes of fuel, the state
    (cl, keys, rf) whose fold over the pairs from cc on is the answer (s7 = keys, the frame's 0x08 = rf). *)
Definition S_WALK (c : pctx) : Prop :=
  forall (r : Z) (n : nat) (cc : Z) (k : option Z) (km : option (list byte)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) (ja jb : list byte),
    st_ok c r -> r + 16 <= cc <= r + 16 + u32_at (c_bs c) (r + 8) + 7 -> cc mod 8 = 0 ->
    (Z.to_nat (r + 16 + u32_at (c_bs c) (r + 8) - cc) < n)%nat ->
    key_ok c k km ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c) (walk_pairs (c_bs c) r cc n km) cl keys rf) = RESM c ->
    PMem c (wframe c rf ja jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 LIT_PREFIX) x21
               (key_reg c k) (Z_to_bv 64 keys) (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8)
               (Z_to_bv 64 (c_P c + r + 8)) (Z_to_bv 64 (c_P c + r + 16)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14e18) fc None m (seg_rom rsegs)).

(** [S_ENTRY]: the call at 0x14cd0, props NULL (null) or the pod: Post for parse_props. *)
Definition S_ENTRY (c : pctx) : Prop :=
  forall (null : bool) (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    frm0 fc ->
    evt rsegs (PPost c (parse_props (parse_arg null (c_bs c)) (c_cap c)))
      (MS (mkR (c_ra c) (c_sp c) (c_gp c) (c_tp c) t0 t1 t2 (c_s0 c) (c_s1 c)
               (Z_to_bv 64 (if null then 0 else c_P c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 (c_cap c))
               (Z_to_bv 64 (c_R c)) a4 a5 a6 a7 (c_s2 c) (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c)
               (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
          F (Z_to_bv 64 HA_PARSE_RESULT) fc None (c_m c) (seg_rom rsegs)).

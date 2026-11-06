(** Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c / pinned 1696d6c34ffd):
    the INTERFACE of its inner walk, 0x13e90 .. 0x141ec and its out-of-line blocks (UBSan binary).
    Statement text only: no function is proved here.

    The inner walk runs main's own code on a concrete machine state (mkR of the cut's registers) and a memory that
    satisfies [V01_env] / [V01_mem]; lib/U/Prog/Seg/V01.v lifts it to [SegEvt.evt_V01] and [SegEnd.seg_V01_stmt]
    through Tac_seg.b1_seg_evt_e (evt_V01 is a seg_evt_e: reac_segconf_declared writes the errno cell).

    The code, by stretch (each stretch is one file, each file one lemma of the Prop below):
    - PREFIX 0x13e90 .. 0x13f94 (lib/U/Prog/Seg/V01Pre.v, delivers [V01_INNER] from [V01_HEAD] and [V01_TAIL]):
      the dead NULL tests of tab and mt; memset(&tab[cap], 0x5a, 18) (the guard); n = 0 at sp+0x5c; 0(sp) = tab;
      when flags & 1 and cap > 0: memcpy(tab, "enp1s0", 7), tab[0].vid = 33 (`sh`), memcpy(mt, "enp1s0", 7),
      mt[0].vid = 33 (`sw`), n = mn = 1; else mn = 0.  Then 0x18(sp) = mt, s3 = m, `lw` m->n:
      m->n <= 0 goes to 0x141a8 (added = 0, the tail); else the loop prologue sets added = 0, i = 0, 8(sp) =
      ~(sp+0x60), 0x30(sp) = 2^50+3, 0x38(sp) = ~mt, s4 = -1, s10 = 4094, s6 = -m, s1 = m, and falls into the head.
    - HEAD 0x13f98 .. 0x13fb4 and JOIN 0x13fb8 .. 0x13fcc (lib/U/Prog/Seg/V01Loop.v, delivers [V01_HEAD] and the
      per-turn [V01_JOINat] by induction on the turns left): the i = 32 and ~m < 256 i traps, s7 = m + 256 i,
      `lw 0x18(s7)` (seg[i].ignore), then the split or the join; the join reloads m->n, i++, s6 -= 256, s1 += 256.
    - SPLIT 0x13fd0 .. 0x140c8 (lib/U/Prog/Seg/V01Split.v, delivers [V01_SPLIT]): m_split inline -- strrchr(name,
      '.'), the dot tests, the digit loop 0x14000 (vid <= 4094, early exits), the parent loop 0x14044 (the
      character test: digits and ':' by (ch-48)&255 < 11, letters by ((ch & ~32)-65)&255 < 26, then '-', '.', '_'
      by the mask 2^50+3 at 0x30(sp)), memcpy(sp+0x60, name, pn), v.parent[pn] = 0, v.vid at sp+0x70.
    - ACC 0x140cc .. 0x1419c, 0x141a0, 0x14254 (lib/U/Prog/Seg/V01Acc.v, delivers [V01_ACC]): the duplicate loop
      over mt[0 .. mn) (the vid `lw` and strcmp, ORed, no early exit), then mn >= cap -> the -1 exit 0x14254, else
      memcpy(&mt[mn], &v, 20), mn++, added++ and the join.
    - TAIL 0x141ac .. 0x141e8 (lib/U/Prog/Seg/V01Tail.v, delivers [V01_TAIL]): reac_segconf_declared(c, tab, cap,
      sp+0x5c) and check_declared(got, want, tab, n, mt, mn, cap), ending at 0x141ec.

    The 15 UBSan trap branches of the segment are all in these stretches and all dead under
    [V01_geo] and the loop invariant: PO tab + 18 cap (0x13ea8), alignment tab & 1 (0x13edc) and mt & 3 (0x13f00,
    0x14100), bounds i = 32 (0x13f9c), PO m + 256 i (0x13fa4), PO dot + 1 (0x13fec) and q + 1 (0x14018), PO
    name + i (0x14044), bounds v.parent[pn] (0x140b0), PO sp+0x60 + pn (0x140b8), PO mt + 20 k (0x140f8), PO
    &mt[mn] (0x14158, 0x14174), signed overflow added++ (0x1418c).

    Statement text of a segment's inner walk. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** This build's addresses (seg_spec.SEG_UBSAN), main's frame and the constants the stretch files share. *)
Definition SA : seg_addrs := SEG_UBSAN.
(** `addi sp,sp,-0xf0` at 0x13888. *)
Definition V01_FRAME : Z := 240.
(** errno_addr B = ms_tp B + ms_errno_off B (Tac_slot.sl_errno_val); the same number as Tac_seg.ERRNO_CELL. *)
Definition V01_ERRNO : Z := 0x335b0 - 164.
(** "enp1s0" in .rodata (0x13ee4 / 0x13f08 auipc+addi). *)
Definition V01_ENP : Z := 0x10539.
(** The '-', '.', ':', '_' bit mask main builds at 0x13f88-0x13f8c and keeps at 0x30(sp). *)
Definition MASK_PARENT : Z := 2 ^ 50 + 3.
(** The pcs of the interface points. *)
Definition V01_PC_IN : Z := 0x13e90.
Definition V01_PC_HEAD : Z := 0x13f98.
Definition V01_PC_JOIN : Z := 0x13fb8.
Definition V01_PC_SPLIT : Z := 0x13fd0.
Definition V01_PC_ACC : Z := 0x140cc.
Definition V01_PC_TAIL : Z := 0x141ac.
Definition V01_PC_OUT : Z := 0x141ec.

(** The ghost context of one run of the segment: the entry sp [S] (so main's sp is S - 240), the four live harness
    blocks, the input bytes, and the parts of the machine the whole stretch keeps (gp, tp, the FP state F and fcsr,
    and the memory [m0] the write set is measured against). Every callee of V01 returns with F and fcsr as it got
    them (memset_c, memcpy_c, strrchr_c, strcmp_c, seg_spec.ret_post / ret_void), so the inner walk keeps them. *)
Record vctx := VCtx {
  v_S : Z;
  v_c : Z;
  v_mm : Z;
  v_tab : Z;
  v_mt : Z;
  v_inp : list byte;
  v_gp : word;
  v_tp : word;
  v_F : bvmap 5 word;
  v_fc : bv 32;
  v_m0 : word -> option byte
}.

Definition v_cap (X : vctx) : Z := seg_cap (v_inp X).
Definition v_flags (X : vctx) : Z := seg_flags (v_inp X).
Definition v_sp (X : vctx) : Z := v_S X - V01_FRAME.
Definition v_lo (X : vctx) : Z := v_S X - 65536.
Definition v_buf (X : vctx) : Z := v_sp X + 0x60.
Definition v_ncell (X : vctx) : Z := v_sp X + 0x5c.
Definition v_ntab (X : vctx) : Z := RVLAN_SIZE * (v_cap X + 1).
Definition v_nmt (X : vctx) : Z := MVLAN_SIZE * (v_cap X + 1).
Definition v_rc (X : vctx) : rconf := seg_rc (run (seg_pay (v_inp X))).
Definition v_mc (X : vctx) : mconf := seg_mc (run (seg_pay (v_inp X))).
Definition v_tab0 (X : vctx) : list (list Z * Z) := seg_tab0 (v_inp X).
Definition v_segs (X : vctx) : list mseg := mc_seg (v_mc X).
Definition v_n0 (X : vctx) : nat := length (v_tab0 X).

(** The bytes the inner walk may write: main's frame up to sp + 0x74 together with the callees' stack below sp
    (one interval [S - 65536, S - 124), inside the slot's window [S - 65536, S - 104)), the two tables, and the
    errno cell (reac_segconf_declared's strtol). It writes neither longl nor the reader block nor the mconf block. *)
Definition V01_W (X : vctx) : list ivl :=
  [(v_lo X, v_S X - 124);
   (v_tab X, v_tab X + v_ntab X);
   (v_mt X, v_mt X + v_nmt X);
   (V01_ERRNO, V01_ERRNO + 4)].

(** ** The numbers of the context (no memory): the frame, the four blocks, their separation and the image cells.
    lib/U/Prog/Seg/V01.v proves every conjunct from FR, P_K13e90 and the slot kit (Tac_b1.b1_hb, b1_blk_noimg_segs,
    Tac_slot.sl_fr_bnd); the stretch files take it as a premise. *)
Definition V01_geo (X : vctx) : Prop :=
  v_S X mod 16 = 0 /\ 0x60000 < v_lo X /\ v_S X <= 2 ^ 47 /\
  bv_unsigned (v_tp X) = 0x335b0 /\
  0 <= v_cap X < 40 /\
  4096 <= v_c X /\ v_c X mod 16 = 0 /\ v_c X + SEG_C_SIZE <= v_lo X /\
  4096 <= v_mm X /\ v_mm X mod 16 = 0 /\ v_mm X + SEG_M_SIZE <= v_lo X /\
  4096 <= v_tab X /\ v_tab X mod 16 = 0 /\ v_tab X + v_ntab X <= v_lo X /\
  4096 <= v_mt X /\ v_mt X mod 16 = 0 /\ v_mt X + v_nmt X <= v_lo X /\
  apart (v_c X) SEG_C_SIZE (v_mm X) (v_mm X + SEG_M_SIZE) /\
  apart (v_c X) SEG_C_SIZE (v_tab X) (v_tab X + v_ntab X) /\
  apart (v_c X) SEG_C_SIZE (v_mt X) (v_mt X + v_nmt X) /\
  apart (v_mm X) SEG_M_SIZE (v_tab X) (v_tab X + v_ntab X) /\
  apart (v_mm X) SEG_M_SIZE (v_mt X) (v_mt X + v_nmt X) /\
  apart (v_tab X) (v_ntab X) (v_mt X) (v_mt X + v_nmt X) /\
  apart V01_ERRNO 4 (v_c X) (v_c X + SEG_C_SIZE) /\
  apart V01_ERRNO 4 (v_mm X) (v_mm X + SEG_M_SIZE) /\
  apart V01_ERRNO 4 (v_tab X) (v_tab X + v_ntab X) /\
  apart V01_ERRNO 4 (v_mt X) (v_mt X + v_nmt X) /\
  apart (sa_guard SA) 8 (v_tab X) (v_tab X + v_ntab X) /\
  apart (sa_guard SA) 8 (v_mt X) (v_mt X + v_nmt X) /\
  apart (sa_got_guard SA) 8 (v_tab X) (v_tab X + v_ntab X) /\
  apart (sa_got_guard SA) 8 (v_mt X) (v_mt X + v_nmt X) /\
  apart V01_ENP 7 (v_tab X) (v_tab X + v_ntab X) /\
  apart V01_ENP 7 (v_mt X) (v_mt X + v_nmt X) /\
  blk_noimg rsegs (v_tab X) (v_ntab X) /\ blk_noimg rsegs (v_mt X) (v_nmt X).

(** ** What every memory of the stretch satisfies and every step keeps.
    The reader block and the mconf block are never written by V01 (the checks and the reader's query take const
    pointers; reac_segconf_declared writes only its frame, the table entries it appends, *n and the errno cell). *)
Definition V01_env (X : vctx) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\
  stk rsegs m (v_lo X) (v_sp X) /\
  (forall a, v_lo X <= a < v_S X -> seg_rom rsegs (wa a) = None) /\
  bytes_at rsegs m (sa_got_guard SA) (le8 (Z_to_bv 64 (sa_guard SA))) /\
  (exists gv : word, bytes_at rsegs m (sa_guard SA) (le8 gv)) /\
  (exists ev : word, rw_cells rsegs m V01_ERRNO [C4 ev]) /\
  bytes_at rsegs m V01_ENP (zb (S_enp ++ [0])) /\
  rconf_at rsegs m (v_c X) (v_rc X) /\
  mconf_at rsegs m (v_mm X) (v_mc X).

(** main's own frame cells, from sp: 0 = tab, 8, 0x10 = cap, 0x18 = mt, 0x20 = added, 0x28 = mn, 0x30, 0x38,
    0x40 = 1 (the "mt is 4-aligned" flag the traps at 0x14100 read), 0x48 = c, 0x50 = m.  Cells 8, 0x30 and 0x38
    are the loop's ~(sp+0x60), 2^50+3 and ~mt from 0x13f80, 0x13f90 and 0x13f68; the tail reads none of the three,
    so they are words of the context there (the m->n <= 0 path of the prefix never writes them). *)
Definition V01_cells (X : vctx) (w8 w30 w38 : word) (added mn : Z) : list cell :=
  [C8 (Z_to_bv 64 (v_tab X));
   C8 w8;
   C8 (Z_to_bv 64 (v_cap X));
   C8 (Z_to_bv 64 (v_mt X));
   C8 (Z_to_bv 64 added);
   C8 (Z_to_bv 64 mn);
   C8 w30;
   C8 w38;
   C8 (Z_to_bv 64 1);
   C8 (Z_to_bv 64 (v_c X));
   C8 (Z_to_bv 64 (v_mm X))].

(** The memory of an interface point: the environment, the frame cells, the int cell *n = length tab0 at sp+0x5c,
    the 20-byte mvlan buffer at sp+0x60, the reader's table tab (set once by the prefix and not touched again
    before the tail), its guard entry and its free entries, the model's table [tb] and its free entries, and the
    write set against m0. *)
Definition V01_mem (X : vctx) (w8 w30 w38 : word) (added : Z) (tb : list (list Z * Z))
    (m : word -> option byte) : Prop :=
  V01_env X m /\
  rw_cells rsegs m (v_sp X) (V01_cells X w8 w30 w38 added (Z.of_nat (length tb))) /\
  (exists jn : list byte, rw_cells rsegs m (v_sp X + 0x58)
     [CB 4 jn; C4 (Z_to_bv 64 (Z.of_nat (v_n0 X)))]) /\
  (exists jb : list byte, rw_cells rsegs m (v_buf X) [CB 20 jb]) /\
  rtab_at rsegs m (v_tab X) (v_tab0 X) /\
  guard_at rsegs m (v_tab X) (v_cap X) /\
  (exists ft : list byte, rw_cells rsegs m (v_tab X + RVLAN_SIZE * Z.of_nat (v_n0 X))
     [CB (Z.to_nat (RVLAN_SIZE * (v_cap X - Z.of_nat (v_n0 X)))) ft]) /\
  mtab_at rsegs m (v_mt X) tb /\
  (exists fm : list byte, rw_cells rsegs m (v_mt X + MVLAN_SIZE * Z.of_nat (length tb))
     [CB (Z.to_nat (MVLAN_SIZE * (v_cap X + 1 - Z.of_nat (length tb)))) fm]) /\
  Z.of_nat (length tb) <= v_cap X /\
  munch (V01_W X) (v_m0 X) m /\ wmono rsegs (v_m0 X) m.

(** The loop's instance: cells 8, 0x30 and 0x38 hold the three constants the loop needs. *)
Definition V01_lmem (X : vctx) (added : Z) (tb : list (list Z * Z)) (m : word -> option byte) : Prop :=
  V01_mem X (Z_to_bv 64 (18446744073709551615 - v_buf X)) (Z_to_bv 64 MASK_PARENT)
            (Z_to_bv 64 (18446744073709551615 - v_mt X)) added tb m.

(** The model invariant at the head of turn i: the table in mt is [tb], [added] entries have been appended, and
    running m_decl_go over the segments left gives the answer m_declared owes (SegModel.m_declared of the mconf
    the state after the file loop holds, over the initial table seg_tab0 inp and the cap). *)
Definition V01_inv (X : vctx) (i : nat) (tb : list (list Z * Z)) (added : Z) : Prop :=
  (i <= length (v_segs X))%nat /\ 0 <= added <= Z.of_nat i /\
  m_decl_go (skipn i (v_segs X)) tb (v_cap X) added = m_declared (v_mc X) (v_tab0 X) (v_cap X).

(** ** The postcondition of the inner walk: at 0x141ec with the registers P_K141ec names (s4 = mt, s2 = tab,
    s3 = m, s0 = c; sp, gp and tp kept), F and fcsr as they were, the writes inside V01_W. *)
Definition V01_post (X : vctx) : machine_state -> Prop :=
  fun ms => exists (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27
                    x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms = MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7
                 (Z_to_bv 64 (v_c X)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (v_tab X)) (Z_to_bv 64 (v_mm X)) (Z_to_bv 64 (v_mt X))
                 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            (v_F X) (Z_to_bv 64 V01_PC_OUT) (v_fc X) None m' (seg_rom rsegs) /\
    munch (V01_W X) (v_m0 X) m' /\ wmono rsegs (v_m0 X) m' /\ mem_inv rsegs m'.

(** ** The interface points.
    Each is "from this state the run reaches V01_post". A stretch proves its own point from the points its code
    can reach; the registers a stretch does not read are universally quantified, so a later stretch may leave
    them as it likes. Register numbers: ra 1, sp 2, gp 3, tp 4, t0-t2 5-7, s0 8, s1 9, a0-a7 10-17, s2-s11 18-27,
    t3-t6 28-31 (mkR takes x1 .. x31 in this order). *)

(** 0x141ac, the tail: after the loop, added = want in 0x20(sp), mn = length wt in 0x28(sp), the model's table wt
    in mt, s3 = m (no instruction between here and 0x141ec writes s3). *)
Definition V01_TAIL (X : vctx) : Prop :=
  forall (want : Z) (wt : list (list Z * Z)) (m : word -> option byte) (w8 w30 w38 : word)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word),
    m_declared (v_mc X) (v_tab0 X) (v_cap X) = (want, wt) ->
    -1 <= want <= 32 ->
    V01_mem X w8 w30 w38 want wt m ->
    evt rsegs (V01_post X)
      (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (v_mm X)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (v_F X) (Z_to_bv 64 V01_PC_TAIL) (v_fc X) None m (seg_rom rsegs)).

(** 0x13fb8, the join after turn i: i turns and the body of turn i are done, the table is tb and added is a. *)
Definition V01_JOINat (X : vctx) (i : nat) : Prop :=
  forall (tb : list (list Z * Z)) (a : Z) (m : word -> option byte)
         (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 : word),
    V01_lmem X a tb m -> V01_inv X (S i) tb a -> (S i <= length (v_segs X))%nat ->
    evt rsegs (V01_post X)
      (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8
               (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (18446744073709551615 - v_mm X))
               (Z_to_bv 64 (v_mm X))
               (Z_to_bv 64 18446744073709551615)
               x21 (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i))) x23 x24
               (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N))
               x28 x29 x30 x31)
          (v_F X) (Z_to_bv 64 V01_PC_JOIN) (v_fc X) None m (seg_rom rsegs)).

(** 0x13f98, the head of turn i (i < m->n). *)
Definition V01_HEADat (X : vctx) (i : nat) : Prop :=
  forall (tb : list (list Z * Z)) (a : Z) (m : word -> option byte)
         (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 : word),
    V01_lmem X a tb m -> V01_inv X i tb a -> (i < length (v_segs X))%nat ->
    evt rsegs (V01_post X)
      (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8
               (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (18446744073709551615 - v_mm X))
               (Z_to_bv 64 (v_mm X))
               (Z_to_bv 64 18446744073709551615)
               x21 (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i))) x23 x24
               (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N))
               x28 x29 x30 x31)
          (v_F X) (Z_to_bv 64 V01_PC_HEAD) (v_fc X) None m (seg_rom rsegs)).

Definition V01_HEAD (X : vctx) : Prop := forall i, V01_HEADat X i.

(** 0x140cc, after m_split accepted: the 20-byte buffer at sp+0x60 holds the mvlan (p, vid) and s0 = vid.
    [p] and [vid] are m_split's answer on the name of segment i (SegModel.m_split). *)
Definition V01_ACCat (X : vctx) (i : nat) : Prop :=
  forall (tb : list (list Z * Z)) (a : Z) (p : list Z) (vid : Z) (bs : list byte)
         (m : word -> option byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word),
    V01_env X m ->
    rw_cells rsegs m (v_sp X)
      (V01_cells X (Z_to_bv 64 (18446744073709551615 - v_buf X)) (Z_to_bv 64 MASK_PARENT)
         (Z_to_bv 64 (18446744073709551615 - v_mt X)) a (Z.of_nat (length tb))) ->
    (exists jn : list byte, rw_cells rsegs m (v_sp X + 0x58)
       [CB 4 jn; C4 (Z_to_bv 64 (Z.of_nat (v_n0 X)))]) ->
    rw_cells rsegs m (v_buf X) [CB 20 bs] -> mvlan_enc (p, vid) bs ->
    rtab_at rsegs m (v_tab X) (v_tab0 X) ->
    guard_at rsegs m (v_tab X) (v_cap X) ->
    (exists ft : list byte, rw_cells rsegs m (v_tab X + RVLAN_SIZE * Z.of_nat (v_n0 X))
       [CB (Z.to_nat (RVLAN_SIZE * (v_cap X - Z.of_nat (v_n0 X)))) ft]) ->
    mtab_at rsegs m (v_mt X) tb ->
    (exists fm : list byte, rw_cells rsegs m (v_mt X + MVLAN_SIZE * Z.of_nat (length tb))
       [CB (Z.to_nat (MVLAN_SIZE * (v_cap X + 1 - Z.of_nat (length tb)))) fm]) ->
    Z.of_nat (length tb) <= v_cap X ->
    munch (V01_W X) (v_m0 X) m -> wmono rsegs (v_m0 X) m ->
    V01_inv X i tb a -> (i < length (v_segs X))%nat ->
    ms_ignore (nth i (v_segs X) mseg_d) = false ->
    m_split (ms_name (nth i (v_segs X) mseg_d)) = Some (p, vid) ->
    0 < vid <= 4094 ->
    evt rsegs (V01_post X)
      (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 (Z_to_bv 64 vid)
               (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (18446744073709551615 - v_mm X))
               (Z_to_bv 64 (v_mm X))
               (Z_to_bv 64 18446744073709551615)
               x21 (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i)))
               (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x24
               (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N))
               x28 x29 x30 x31)
          (v_F X) (Z_to_bv 64 V01_PC_ACC) (v_fc X) None m (seg_rom rsegs)).

(** 0x13fd0, the body of turn i when seg[i].ignore is 0: s7 = m + 256 i as well. *)
Definition V01_SPLITat (X : vctx) (i : nat) : Prop :=
  forall (tb : list (list Z * Z)) (a : Z) (m : word -> option byte)
         (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word),
    V01_lmem X a tb m -> V01_inv X i tb a -> (i < length (v_segs X))%nat ->
    ms_ignore (nth i (v_segs X) mseg_d) = false ->
    evt rsegs (V01_post X)
      (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8
               (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (18446744073709551615 - v_mm X))
               (Z_to_bv 64 (v_mm X))
               (Z_to_bv 64 18446744073709551615)
               x21 (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i)))
               (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x24
               (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N))
               x28 x29 x30 x31)
          (v_F X) (Z_to_bv 64 V01_PC_SPLIT) (v_fc X) None m (seg_rom rsegs)).

(** The two stretches inside a turn, each with the continuations its code reaches. *)
Definition V01_SPLIT (X : vctx) : Prop := forall i, V01_JOINat X i -> V01_ACCat X i -> V01_SPLITat X i.
Definition V01_ACC (X : vctx) : Prop := forall i, V01_JOINat X i -> V01_TAIL X -> V01_ACCat X i.

(** 0x13e90, the entry of the segment: the registers P_K13e90 names (a0 = mt, s1 = tab, s4 = cap + 1, s0 = cap,
    s2 = ~m, s11 = m + 0x2000) and the memory the two callocs left. The free entries of both tables are the whole
    block (they are zero: rw_cells is their writability) and the reader's table is still empty. *)
Definition V01_INNER (X : vctx) : Prop :=
  forall (m : word -> option byte)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (fcell0 fcell8 fcell18 fcell20 fcell28 fcell30 fcell38 fcell40 : word) (j58 : list byte),
    V01_env X m ->
    munch (V01_W X) (v_m0 X) m -> wmono rsegs (v_m0 X) m ->
    rw_cells rsegs m (v_sp X)
      [C8 fcell0; C8 fcell8; C8 (Z_to_bv 64 (v_cap X)); C8 fcell18; C8 fcell20; C8 fcell28; C8 fcell30;
       C8 fcell38; C8 fcell40; C8 (Z_to_bv 64 (v_c X)); C8 (Z_to_bv 64 (v_mm X))] ->
    fcell8 = Z_to_bv 64 (v_flags X) -> fcell20 = Z_to_bv 64 (v_cap X) ->
    (exists jn : list byte, rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; CB 4 j58]) ->
    (exists jb : list byte, rw_cells rsegs m (v_buf X) [CB 20 jb]) ->
    bytes_at rsegs m (v_tab X) (repeat ZERO (Z.to_nat (v_ntab X))) ->
    bytes_at rsegs m (v_mt X) (repeat ZERO (Z.to_nat (v_nmt X))) ->
    (exists ft : list byte, rw_cells rsegs m (v_tab X) [CB (Z.to_nat (v_ntab X)) ft]) ->
    (exists fm : list byte, rw_cells rsegs m (v_mt X) [CB (Z.to_nat (v_nmt X)) fm]) ->
    evt rsegs (V01_post X)
      (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 (Z_to_bv 64 (v_cap X))
               (Z_to_bv 64 (v_tab X)) (Z_to_bv 64 (v_mt X)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (18446744073709551615 - v_mm X))
               x19
               (Z_to_bv 64 (v_cap X + 1))
               x21 x22 x23 x24 x25 x26
               (Z_to_bv 64 (v_mm X + MC_N))
               x28 x29 x30 x31)
          (v_F X) (Z_to_bv 64 V01_PC_IN) (v_fc X) None m (seg_rom rsegs)).

(** reac-pw/fuzz_segconf, the build (3776ca44d75c): the semantic part P of each cut of LLVMFuzzerTestOneInput, as
    the slot's SlotInv.v takes it (the P parameter of its CUTST: pin's Prog/SlotInv.v form). One Definition
    per cut, over the input bytes [inp] (the ghost g_in), the input block's address
    [p] (g_p), the entry stack pointer [Sp] (g_S), the live blocks' addresses and sizes, the cut's registers and its
    memory. This file Requires only
    Lib, the build's Img0, Spec/SegModel.v, Prog/seg_spec.v and Reusable/YK11 (for getr, the register reader the
    slot's CUTST uses), never SlotFR or SlotInv, so the two build apart. The block list hb, the frame FR,
    the permutation and the global invariant GI (longl's byte 120) are the slot's; P says nothing about them.
    Statement text only: no function is proved here.

    The payload's quantities (cap, flags, nfiles, the cursor
    after k records, each turn's lb, length and text, the states after k turns) are seg_spec.seg_* over
    SegModel.decode of the input bytes. Register numbers: ra 1, sp 2, gp 3, tp 4, s0 8, s1 9, a0-a7 10-17,
    s2-s11 18-27. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
Import ListNotations.
Open Scope Z_scope.

Definition SA : seg_addrs := SEG_PLAIN.
Definition SEG_FRAME : Z := 208.
Definition ENTRY : Z := 0x137c4.
Definition CUT_K138a4 : Z := 0x138a4.
Definition CUT_K138e8 : Z := 0x138e8.
Definition CUT_K13984 : Z := 0x13984.
Definition CUT_K13ad8 : Z := 0x13ad8.
Definition CUT_K13ae0 : Z := 0x13ae0.
Definition CUT_K13cac : Z := 0x13cac.
Definition CUT_K13f40 : Z := 0x13f40.
Definition RET : Z := 0x13f9c.

(** A register holds the word of v. *)
Definition rgz (regs : bvmap 5 word) (r : reg) (v : Z) : Prop := getr regs r = Z_to_bv 64 v.
(** A frame cell of main's own frame (sp = Sp - SEG_FRAME) holds the 8 bytes of v. *)
Definition celz (m : word -> option byte) (Sp off v : Z) : Prop :=
  bytes_at rsegs m (Sp - SEG_FRAME + off) (le8 (Z_to_bv 64 v)).
(** The sizes of the two tables (H:649-650), (cap + 1) entries of 18 and 20 bytes. *)
Definition TAB_N (inp : list byte) : Z := RVLAN_SIZE * (seg_cap inp + 1).
Definition MT_N (inp : list byte) : Z := MVLAN_SIZE * (seg_cap inp + 1).
(** The text block of turn k: its n + 1 bytes (fuzz.h:89). *)
Definition TXT_N (inp : list byte) (k : nat) : Z := seg_txt_n inp k + 1.
(** The label format "reac-pw.conf.d/%u-x.conf" in .rodata, at the same address in both images
    (plain 0x138d4-0x138d8 `auipc`/`addi`, UBSan 0x139cc-0x139d4). *)
Definition LABEL_FMT : Z := 0x1093b.

(** ** The facts every cut from the loop head on carries
    Main keeps c, m and the payload's values in callee-saved registers and in its own frame; the walks read them
    back after every call. The stores are 0x138b0 (0x18 = cap), 0x138b8 (0x10 = cap & 0xff = cap), 0x138bc
    (s10 = m + 0x2000), 0x138d0 (0x20 = m + 0x10), 0x138dc (0x28 = the label format), 0x138e4 (0x30 = c), and
    0x13858 (8 = flags). *)
Definition P_mcore (inp : list byte) (p Sp : Z) (c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  rgz regs 8 mm /\ rgz regs 26 (mm + MC_N) /\
  celz mem Sp 8 (seg_flags inp) /\ celz mem Sp 0x10 (seg_cap inp) /\ celz mem Sp 0x30 c /\
  c mod 16 = 0 /\ mm mod 16 = 0 /\ blk_noimg rsegs c SEG_C_SIZE /\ blk_noimg rsegs mm SEG_M_SIZE.
(** The extra cells and registers the file loop reads and that are overwritten after it (0x18 becomes `added`,
    0x20 becomes mt, 0x28 becomes m_split's bit mask). *)
Definition P_lcore (inp : list byte) (p Sp : Z) (c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  P_mcore inp p Sp c mm regs mem /\ rgz regs 18 (seg_nfiles inp) /\
  celz mem Sp 0x18 (seg_cap inp) /\ celz mem Sp 0x20 (mm + 0x10) /\ celz mem Sp 0x28 LABEL_FMT.

(** ** ENTRY (0x137c4)
    Not a cut parameter of the slot (the slot's Inv_ENTRY is the frame's lib_pre plus GI); it is what the E01 walk
    proves from lib_pre: a0 = the input block, a1 = its length, sp = Sp. *)
Definition P_ENTRY (inp : list byte) (p Sp : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  rgz regs 10 p /\ rgz regs 11 (Z.of_nat (length inp)) /\ rgz regs 2 Sp.

(** ** K138a4 (0x138a4): calloc(1, 9236)'s return, hb = [(m, 9236); (c, 16616)]
    c's 16616 bytes are present and writable but unknown (reac_segconf_init follows); m's 9236 bytes are all zero
    (calloc). The cursor is past the three header u8 (cap, flags, nfiles). *)
Definition P_K138a4 (inp : list byte) (p Sp c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  rgz regs 10 mm /\ rgz regs 24 c /\ rgz regs 9 (seg_cap inp) /\ rgz regs 18 (seg_nfiles inp) /\
  rgz regs 19 (seg_cur_at inp p 0) /\ rgz regs 21 (seg_cur_n inp 0) /\ rgz regs 26 MC_N /\
  celz mem Sp 8 (seg_flags inp) /\
  (exists junk, rw_cells rsegs mem c [CB (Z.to_nat SEG_C_SIZE) junk]) /\
  bytes_at rsegs mem mm (repeat ZERO (Z.to_nat SEG_M_SIZE)) /\
  c mod 16 = 0 /\ mm mod 16 = 0 /\ blk_noimg rsegs c SEG_C_SIZE /\ blk_noimg rsegs mm SEG_M_SIZE.

(** ** K138e8 (0x138e8): the file-loop head, turn f, hb = [(m, 9236); (c, 16616)]
    c and m hold the reader's and the model's states after the f drop-in turns already run (seg_spec.seg_run), s4 is
    the AND of `parse_file(..) == m->n` over them, and the cursor stands after f records. The frame cells: 8 flags,
    0x10 the cap byte, 0x18 cap, 0x20 m + 0x10, 0x28 the label format pointer, 0x30 c. *)
Definition P_K138e8 (inp : list byte) (p Sp : Z) (f : nat) (c mm : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  Z.of_nat f < seg_nfiles inp /\ P_lcore inp p Sp c mm regs mem /\
  rgz regs 27 (Z.of_nat f) /\
  rgz regs 19 (seg_cur_at inp p f) /\ rgz regs 21 (seg_cur_n inp f) /\
  rgz regs 20 (b2z (seg_ret (seg_run inp f))) /\
  rconf_at rsegs mem c (seg_rc (seg_run inp f)) /\ mconf_at rsegs mem mm (seg_mc (seg_run inp f)).

(** ** K13984 (0x13984): malloc(n + 1)'s return, hb = [(t, nt); (m, 9236); (c, 16616)]
    The text block's nt = n + 1 bytes are present and writable but unknown (the memcpy and the NUL follow). s3 and s5
    still point at the bytes fuzz_take took and the count before the take; s9 = n, s6 = n', s8 = lb. *)
Definition P_K13984 (inp : list byte) (p Sp : Z) (f : nat) (c mm t nt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  Z.of_nat f < seg_nfiles inp /\ P_lcore inp p Sp c mm regs mem /\
  rgz regs 27 (Z.of_nat f) /\ rgz regs 20 (b2z (seg_ret (seg_run inp f))) /\
  rconf_at rsegs mem c (seg_rc (seg_run inp f)) /\ mconf_at rsegs mem mm (seg_mc (seg_run inp f)) /\
  nt = TXT_N inp f /\
  rgz regs 10 t /\ t mod 16 = 0 /\ blk_noimg rsegs t nt /\
  (exists junk, rw_cells rsegs mem t [CB (Z.to_nat nt) junk]) /\
  rgz regs 25 (seg_txt_n inp f) /\ rgz regs 22 (seg_turn_np inp f) /\
  rgz regs 19 (seg_turn_at inp p f) /\ rgz regs 21 (Z.of_nat (length (seg_turn_tail inp f))) /\
  rgz regs 24 (seg_lb inp f).

(** ** K13ad8 (0x13ad8): `jal free(text)`, hb = [(t, nt); (m, 9236); (c, 16616)]
    Turn f has run: c and m hold seg_spec.seg_after inp f (the drop-in step, or m_cross and reac_segconf_parse on the
    last turn), s11 = f + 1, the cursor stands after f + 1 records, s4 is the running AND. *)
Definition P_K13ad8 (inp : list byte) (p Sp : Z) (f : nat) (c mm t nt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  Z.of_nat f < seg_nfiles inp /\ nt = TXT_N inp f /\ P_lcore inp p Sp c mm regs mem /\
  rgz regs 10 t /\ rgz regs 23 t /\ rgz regs 27 (Z.of_nat (Nat.succ f)) /\
  rgz regs 19 (seg_cur_at inp p (Nat.succ f)) /\ rgz regs 21 (seg_cur_n inp (Nat.succ f)) /\
  rgz regs 20 (b2z (seg_ret (seg_after inp f))) /\ rgz regs 24 c /\
  rconf_at rsegs mem c (seg_rc (seg_after inp f)) /\ mconf_at rsegs mem mm (seg_mc (seg_after inp f)).

(** ** K13ae0 (0x13ae0): after the file loop, hb = [(m, 9236); (c, 16616)]
    Every file has been read and m_cross has run on the last turn: c and m hold SegModel.run of the payload, and s4
    is its [returned]. *)
Definition P_K13ae0 (inp : list byte) (p Sp c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  P_mcore inp p Sp c mm regs mem /\ rgz regs 24 c /\ celz mem Sp 0x18 (seg_cap inp) /\
  rgz regs 20 (b2z (seg_ret (run (seg_pay inp)))) /\
  rconf_at rsegs mem c (seg_rc (run (seg_pay inp))) /\ mconf_at rsegs mem mm (seg_mc (run (seg_pay inp))).

(** ** K13cac (0x13cac): calloc(cap + 1, 20)'s return, hb = [(mt, nmt); (tab, ntab); (m, 9236); (c, 16616)]
    Both tables are all zero (calloc); c and m are what they were after the loop (the ten check_* and the reader's
    queries read them and write nothing). *)
Definition P_K13cac (inp : list byte) (p Sp c mm tab ntab mt nmt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  ntab = TAB_N inp /\ nmt = MT_N inp /\ P_mcore inp p Sp c mm regs mem /\
  rgz regs 10 mt /\ rgz regs 19 tab /\ rgz regs 20 (seg_cap inp + 1) /\ rgz regs 22 (seg_cap inp) /\
  bytes_at rsegs mem tab (repeat ZERO (Z.to_nat ntab)) /\ bytes_at rsegs mem mt (repeat ZERO (Z.to_nat nmt)) /\
  tab mod 16 = 0 /\ mt mod 16 = 0 /\ blk_noimg rsegs tab ntab /\ blk_noimg rsegs mt nmt /\
  rconf_at rsegs mem c (seg_rc (run (seg_pay inp))) /\ mconf_at rsegs mem mm (seg_mc (run (seg_pay inp))).

(** ** K13f40 (0x13f40): before the four frees, hb = [(mt, nmt); (tab, ntab); (m, 9236); (c, 16616)]
    A register map only: the four blocks are freed newest first (H:667-670). *)
Definition P_K13f40 (inp : list byte) (p Sp c mm tab ntab mt nmt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  ntab = TAB_N inp /\ nmt = MT_N inp /\
  rgz regs 20 mt /\ rgz regs 19 tab /\ rgz regs 8 mm /\ rgz regs 9 c.

(** reac-pw/fuzz_segconf, the UBSan build (1696d6c34ffd): the semantic part P of each cut of LLVMFuzzerTestOneInput, as
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
Import ListNotations.
Open Scope Z_scope.

Definition SA : seg_addrs := SEG_UBSAN.
Definition SEG_FRAME : Z := 240.
Definition ENTRY : Z := 0x13888.
Definition CUT_K13984 : Z := 0x13984.
Definition CUT_K139e4 : Z := 0x139e4.
Definition CUT_K13aac : Z := 0x13aac.
Definition CUT_K13c34 : Z := 0x13c34.
Definition CUT_K13c3c : Z := 0x13c3c.
Definition CUT_K13e90 : Z := 0x13e90.
Definition CUT_K141ec : Z := 0x141ec.
Definition RET : Z := 0x14248.

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
    The stores are 0x13994 (8 = flags), 0x13998 (0x20 = cap), 0x139a0 (0x10 = cap & 0xff = cap), 0x139a4
    (s11 = m + 0x2000), 0x139b8 (0x38 = m & 3), 0x139bc (s2 = ~m), 0x139c0 (0x50 = m), 0x139c8 (0x28 = m + 0x10),
    0x139d0 (s5 = 33), 0x139d8 (0x30 = the label format), 0x139e0 (0x40 = nfiles), 0x13984 (0x48 = c). *)
Definition P_mcore (inp : list byte) (p Sp : Z) (c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 18 = bv_not (Z_to_bv 64 mm) /\ rgz regs 27 (mm + MC_N) /\
  celz mem Sp 8 (seg_flags inp) /\ celz mem Sp 0x10 (seg_cap inp) /\ celz mem Sp 0x20 (seg_cap inp) /\
  celz mem Sp 0x48 c /\ celz mem Sp 0x50 mm /\
  c mod 16 = 0 /\ mm mod 16 = 0 /\ blk_noimg rsegs c SEG_C_SIZE /\ blk_noimg rsegs mm SEG_M_SIZE.
(** The extra cells and registers the file loop reads (0x38 becomes mt's alignment flag and 0x40 is reused after
    the loop). *)
Definition P_lcore (inp : list byte) (p Sp : Z) (c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  P_mcore inp p Sp c mm regs mem /\ rgz regs 21 33 /\
  celz mem Sp 0x28 (mm + 0x10) /\ celz mem Sp 0x30 LABEL_FMT /\
  celz mem Sp 0x38 (mm mod 4) /\ celz mem Sp 0x40 (seg_nfiles inp).

(** ** ENTRY (0x13888)
    Not a cut parameter of the slot; what the E01 walk proves from lib_pre. *)
Definition P_ENTRY (inp : list byte) (p Sp : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  rgz regs 10 p /\ rgz regs 11 (Z.of_nat (length inp)) /\ rgz regs 2 Sp.

(** ** K13984 (0x13984): calloc(1, 9236)'s return, hb = [(m, 9236); (c, 16616)]
    As the plain build's K138a4, with the UBSan register map: s0 = c, s2 = cap, s5 = flags,
    s6 = nfiles, s3 and s1 the cursor, s11 = 0x2000. *)
Definition P_K13984 (inp : list byte) (p Sp c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  rgz regs 10 mm /\ rgz regs 8 c /\ rgz regs 18 (seg_cap inp) /\ rgz regs 21 (seg_flags inp) /\
  rgz regs 22 (seg_nfiles inp) /\
  rgz regs 19 (seg_cur_at inp p 0) /\ rgz regs 9 (seg_cur_n inp 0) /\ rgz regs 27 MC_N /\
  (exists junk, rw_cells rsegs mem c [CB (Z.to_nat SEG_C_SIZE) junk]) /\
  bytes_at rsegs mem mm (repeat ZERO (Z.to_nat SEG_M_SIZE)) /\
  c mod 16 = 0 /\ mm mod 16 = 0 /\ blk_noimg rsegs c SEG_C_SIZE /\ blk_noimg rsegs mm SEG_M_SIZE.

(** ** K139e4 (0x139e4): the file-loop head, turn f, hb = [(m, 9236); (c, 16616)]
    The UBSan map: s0 = f, 0x40(sp) = nfiles, s3 and s1 the cursor, s4 = returned, s2 = ~m (the no-wrap material),
    s5 = 33, s11 = &m->n, 0x38(sp) = m & 3, 0x48(sp) = c, 0x50(sp) = m. *)
Definition P_K139e4 (inp : list byte) (p Sp : Z) (f : nat) (c mm : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  Z.of_nat f < seg_nfiles inp /\ P_lcore inp p Sp c mm regs mem /\
  rgz regs 8 (Z.of_nat f) /\
  rgz regs 19 (seg_cur_at inp p f) /\ rgz regs 9 (seg_cur_n inp f) /\
  rgz regs 20 (b2z (seg_ret (seg_run inp f))) /\
  rconf_at rsegs mem c (seg_rc (seg_run inp f)) /\ mconf_at rsegs mem mm (seg_mc (seg_run inp f)).

(** ** K13aac (0x13aac): malloc(n + 1)'s return, hb = [(t, nt); (m, 9236); (c, 16616)]
    s10 = n, s6 = n', s9 = the take's address, s3 = that address + n', s1 = the count before the take, s8 = lb. *)
Definition P_K13aac (inp : list byte) (p Sp : Z) (f : nat) (c mm t nt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  Z.of_nat f < seg_nfiles inp /\ nt = TXT_N inp f /\ P_lcore inp p Sp c mm regs mem /\
  rgz regs 10 t /\ t mod 16 = 0 /\ blk_noimg rsegs t nt /\
  (exists junk, rw_cells rsegs mem t [CB (Z.to_nat nt) junk]) /\
  rgz regs 26 (seg_txt_n inp f) /\ rgz regs 22 (seg_turn_np inp f) /\
  rgz regs 25 (seg_turn_at inp p f) /\ rgz regs 19 (seg_turn_at inp p f + seg_turn_np inp f) /\
  rgz regs 9 (Z.of_nat (length (seg_turn_tail inp f))) /\ rgz regs 24 (seg_lb inp f) /\
  rgz regs 8 (Z.of_nat f) /\ rgz regs 20 (b2z (seg_ret (seg_run inp f))) /\
  rconf_at rsegs mem c (seg_rc (seg_run inp f)) /\ mconf_at rsegs mem mm (seg_mc (seg_run inp f)).

(** ** K13c34 (0x13c34): `jal free(text)`, hb = [(t, nt); (m, 9236); (c, 16616)]
    Turn f has run (seg_spec.seg_after); s0 = f + 1, s1 = the count left, s10 = nfiles. *)
Definition P_K13c34 (inp : list byte) (p Sp : Z) (f : nat) (c mm t nt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  Z.of_nat f < seg_nfiles inp /\ nt = TXT_N inp f /\ P_lcore inp p Sp c mm regs mem /\
  rgz regs 10 t /\ rgz regs 23 t /\ rgz regs 8 (Z.of_nat (Nat.succ f)) /\
  rgz regs 19 (seg_cur_at inp p (Nat.succ f)) /\ rgz regs 9 (seg_cur_n inp (Nat.succ f)) /\
  rgz regs 20 (b2z (seg_ret (seg_after inp f))) /\ rgz regs 26 (seg_nfiles inp) /\
  rconf_at rsegs mem c (seg_rc (seg_after inp f)) /\ mconf_at rsegs mem mm (seg_mc (seg_after inp f)).

(** ** K13c3c (0x13c3c): after the file loop, hb = [(m, 9236); (c, 16616)] *)
Definition P_K13c3c (inp : list byte) (p Sp c mm : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  P_mcore inp p Sp c mm regs mem /\ celz mem Sp 0x38 (mm mod 4) /\
  rgz regs 20 (b2z (seg_ret (run (seg_pay inp)))) /\
  rconf_at rsegs mem c (seg_rc (run (seg_pay inp))) /\ mconf_at rsegs mem mm (seg_mc (run (seg_pay inp))).

(** ** K13e90 (0x13e90): calloc(cap + 1, 20)'s return, hb = [(mt, nmt); (tab, ntab); (m, 9236); (c, 16616)] *)
Definition P_K13e90 (inp : list byte) (p Sp c mm tab ntab mt nmt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  ntab = TAB_N inp /\ nmt = MT_N inp /\ P_mcore inp p Sp c mm regs mem /\
  rgz regs 10 mt /\ rgz regs 9 tab /\ rgz regs 20 (seg_cap inp + 1) /\ rgz regs 8 (seg_cap inp) /\
  bytes_at rsegs mem tab (repeat ZERO (Z.to_nat ntab)) /\ bytes_at rsegs mem mt (repeat ZERO (Z.to_nat nmt)) /\
  tab mod 16 = 0 /\ mt mod 16 = 0 /\ blk_noimg rsegs tab ntab /\ blk_noimg rsegs mt nmt /\
  rconf_at rsegs mem c (seg_rc (run (seg_pay inp))) /\ mconf_at rsegs mem mm (seg_mc (run (seg_pay inp))).

(** ** K141ec (0x141ec): before the four frees *)
Definition P_K141ec (inp : list byte) (p Sp c mm tab ntab mt nmt : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  ntab = TAB_N inp /\ nmt = MT_N inp /\
  rgz regs 20 mt /\ rgz regs 18 tab /\ rgz regs 19 mm /\ rgz regs 8 c.

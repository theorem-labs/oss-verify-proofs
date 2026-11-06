(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryDefs.v, with its module paths, module names and numbers changed; 162 of its 239 lines of code are new or changed and 283 lines of the source are left out. *)
(* The walk of fuzz_boxreg's entry function LLVMFuzzerTestOneInput (fuzz_boxreg.asan 0x7ff4c, 1065 instructions)
   on the ASan build, cut into phases: the data every phase shares. The phases prove `tfib_lib_contract_x_all`
   (lib/A/Prog/BoxLibX.v); the shape of the cut follows fuzz_grant's entry walk (a working branch
   GrantEntryDefs.v), which follows cgif_file_fuzzer's lib/A/ACf5.v.

   The function keeps two frames at once:
   - a machine-stack frame of 256 bytes (`addi sp,sp,-0x100` at 0x7ff4c), which holds ra, s0 .. s11 at the caller's
     sp - 8 .. sp - 104 and, from the 32-byte realignment (`andi sp,sp,-0x20` at 0x7ff8c) up, the spill slots
     [sp1, sp1 + 0x98) the body reads back; s1 holds sp1 and s0 the caller's sp;
   - a frame on the side stack, class 3 (512-byte slots), taken by `__asan_stack_malloc_3` (a0 = 0x1a0) at 0x7ffbc,
     since the image's use-after-return flag is set (AR's constant cell, BoxFrame.v uar_cell_regionP). The frame F
     (in s6 and at sp1 + 0x18, 0x28, 0x80) holds the frame header at F .. F + 23, `uint8_t mac[6]` at F + 0x20 and
     `struct reac_boxreg prev` (288 bytes) at F + 0x40; its 52 shadow bytes start at SHADOW_OFF + F / 8 (s8); the
     slot's flag address is the word at F + 504.

   Cuts (pc offsets from 0x7ff4c, the listing's base):
     J  0x2a0 (0x801ec)  the head of the operation loop: `i` operations done; the table r holds bs.
     T  0x3a0 / 0x45c / 0x408 / 0x4b0 (0x802ec / 0x803a8 / 0x80354 / 0x803fc)  the case of op & 3 = 0 / 1 / 2 / 3:
                         op is read, prev is a copy of the table, the frame's objects are in scope.
     K  0xb68 (0x80ab4)  the join: the case is done, `check (r, fabric)` and `check_kept` follow.
     X  0xec8 (0x80e14)  the loop is done: `free (r)`, then the frame is given back and the function returns.
   The early return of an input of FUZZ_INPUT_MAX = 2^26 bytes or more (0x80104 -> 0x80e24) is not a cut: the
   contract's pre-condition has n < 2^26, so the branch is never taken.

   One phase = one file (BoxLxEntry, BoxLxHead, BoxLxCase0 .. 3, BoxLxJoin, BoxLxExit); the cut between two phases is
   semantic (a predicate on the machine state, `gb_from` below), never a symbolic state. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg LLVMFuzzerTestOneInput_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the function's stack, its frame on the side stack, and its event budget ---- *)

(* The machine stack the call needs, its event and live-byte budgets, and the driver's empty buffer: the values
   BoxLibX.v states (LLVMF_STK, EV_LIB, LIVE_LIB, A_EMPTY); `BoxLibX.v` closes the walk with these equalities. *)
Definition GB_STK : Z := 32768.
Definition GB_EV : Z := 2000.
Definition GB_LIVE : Z := 2 ^ 33.
Definition GB_EMPTY : Z := 0x5d35e0.
(* The class of the side-stack frame: `__asan_stack_malloc_3`, 512-byte slots; the function's own 416 bytes and its
   52 shadow bytes. *)
Definition GB_CID : Z := 3.
Definition GB_FRAME : Z := 416.
Definition GB_NSH : nat := 52%nat.
(* The objects of the frame (the shadow stores at 0x80028 .. 0x80100). *)
Definition GO_MAC : Z := 32.      (* uint8_t mac[6]          *)
Definition GO_PREV : Z := 64.     (* struct reac_boxreg prev *)

(* The 52 shadow bytes of the frame. GSH_J: as the prologue leaves them, and as the join leaves them again at the end
   of each turn (0x80c40 .. 0x80cdc): 0xf1 left redzone, 0xf8 an object out of scope (mac, prev), 0xf2 between two
   objects, 0xf3 right redzone. GSH_it: inside a turn, mac (6 bytes, 0x80220) and prev (0x80234 .. 0x802c0) in
   scope. *)
Definition GSH_J : list Z :=
  [241; 241; 241; 241; 248; 242; 242; 242] ++ repeat 248 36 ++ repeat 243 8.
Definition GSH_it : list Z :=
  [241; 241; 241; 241; 6; 242; 242; 242] ++ repeat 0 36 ++ repeat 243 8.

(* ---- the pcs of the cuts, as offsets in the listing (address - 0x7ff4c) ---- *)
Definition GP_entry : Z := 0x0.        (* 0x7ff4c, the first slot                      *)
Definition GP_J : Z := 0x2a0.          (* 0x801ec, the head of the operation loop      *)
Definition GP_T (op3 : Z) : Z :=       (* 0x802ec / 0x803a8 / 0x80354 / 0x803fc         *)
  if op3 =? 0 then 0x3a0 else if op3 =? 1 then 0x45c else if op3 =? 2 then 0x408 else 0x4b0.
Definition GP_K : Z := 0xb68.          (* 0x80ab4, the join                             *)
Definition GP_X : Z := 0xec8.          (* 0x80e14, free (r), then the return            *)

(* The call sites whose call trace the allocator's contracts ask for: the return address of the function's one call
   of the malloc wrapper (0x80118) and of its three calls of the free wrapper (0x805fc case 3, 0x80aa8 case 0,
   0x80e18 the exit), as offsets in the listing. *)
Definition GB_MSITES : list Z := [0x1d0].
Definition GB_FSITES : list Z := [0x6b4; 0xb60; 0xed0].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

(* The program's registered globals (fuzz_boxreg.asan's asan_globals, five records), as (address, size) over the
   listing's objects: ZERO (A_OBJ 6, 0x20cc0, 6 bytes), the "" of fuzz_boxreg.c:266 / 394 (A_OBJ 5, 0x20ce0, 1),
   read_mac's base (A_OBJ 4, 0x20d00, 5), "%s" (A_OBJ 10, 0x20d40, 3) and "" (A_OBJ 11, 0x20d60, 1). A phase takes
   `globs_marked SEGS B BX_G` (BoxRo.v) for their shadow. *)
Definition BX_G : list (Z * Z) :=
  [(VAL (A_OBJ 6), 6); (VAL (A_OBJ 5), 1); (VAL (A_OBJ 4), 5); (VAL (A_OBJ 10), 3); (VAL (A_OBJ 11), 1)].

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the entry function's context: what the call starts from ---- *)
Record bcx := mkBCX {
  c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word;
  c_mem : word -> option byte; c_md : Model;
  c_p : Z;                   (* the caller's input buffer                    *)
  c_pl : list byte;          (* its bytes                                    *)
  c_sp1 : Z;                 (* the realigned machine stack pointer, s1      *)
  c_E0 : env;                (* the atoms of the entry registers             *)
  c_T : Z                    (* the allocator budget the caller grants       *)
}.
Definition c_n (cx : bcx) : Z := Z.of_nat (length (c_pl cx)).

(* The frame this call owns on the side stack, its flag, and its shadow. *)
Definition gF (cx : bcx) (fp : Z) : Z := frame_addr (c_ly cx) GB_CID fp.
Definition gFL (cx : bcx) (fp : Z) : Z := flag_addr (c_ly cx) GB_CID fp.
Definition gSH (cx : bcx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (gF cx fp).

(* What the call may spend with the allocator: the registry (288 bytes) at the start, then in each of at most 64
   turns one name (read_name: 1 .. 48 bytes) and its free, and the free of the registry at the end. *)
Definition GB_A (i : Z) : Z := mo_malloc MT 288 + i * (mo_malloc MT 48 + mo_free MT).
Definition GB_NEED : Z := GB_A 64 + mo_free MT.

(* The call chain this call hands to the functions it calls (cgif_file lib/A/ACf5.v:128-131). *)
Definition gch (cx : bcx) : list (Z * Z * Z) :=
  if spZ (c_regs cx) + 16 <? ly_top (c_ly cx)
  then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].

Definition gb_base (cx : bcx) : Prop :=
  afn_pre SEGS B GB_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
  getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
  ((c_n cx = 0 /\ c_p cx = GB_EMPTY) \/
   (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
  garr8 SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  frames (c_S cx) = [] /\
  st_nev (c_S cx) + GB_EV <= EV_MAX /\ blocks_bytes (c_S cx) + GB_LIVE <= LIVE_MAX /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
  c_sp1 cx = 32 * ((spZ (c_regs cx) + -256) / 32) /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
  bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
  ew (c_E0 cx) 32 = w64 SHADOW_OFF /\
  mo_ok MT (c_S cx) (c_T cx) /\
  (forall pcf (regsT : bvmap 5 word),
     (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - BASE) GB_MSITES) \/
     (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - BASE) GB_FSITES) ->
     In (call_trace0 pcf regsT (gch cx)) (as_universe B)) /\
  GB_NEED <= c_T cx.

(* ---- the memory of a phase ---- *)

(* The shadow bytes of the frame. *)
Definition gshadow (cx : bcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + Z.of_nat i) = Some (nth i sh 0).

(* A spill slot of the machine frame: the body reads these back after every call. *)
Definition gslot (cx : bcx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some v.

(* The slots that name the frame and its objects (0x7fff0, 0x80108, 0x8015c, 0x80164, 0x80198). *)
Definition gslots_fr (cx : bcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  gslot cx W3 ms3 0x18 (gF cx fp) /\
  gslot cx W3 ms3 0x28 (gF cx fp) /\
  gslot cx W3 ms3 0x70 (gF cx fp + GO_MAC) /\
  gslot cx W3 ms3 0x78 (gF cx fp + GO_PREV) /\
  gslot cx W3 ms3 0x80 (gF cx fp).

(* The slots the loop's set-up (0x801ac .. 0x801e8) adds for the table r and the fabric: the partial-granule bound
   of r->n's shadow test ((r + 280) mod 8 + 3 = 3: r is 16-aligned), &prev.box[0].nch, the shadow of r->box[0].base,
   &r->n and its shadow, and the fabric. *)
Definition gslots_r (cx : bcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (r fab : Z) : Prop :=
  gslot cx W3 ms3 0x10 3 /\
  gslot cx W3 ms3 0x20 (gF cx fp + GO_PREV + 12) /\
  gslot cx W3 ms3 0x38 (shadow_of_addr SHADOW_OFF (r + 8)) /\
  gslot cx W3 ms3 0x40 (r + 280) /\
  gslot cx W3 ms3 0x50 fab /\
  gslot cx W3 ms3 0x60 (shadow_of_addr SHADOW_OFF (r + 280)).

(* The input cursor `struct fuzz_in in` at sp1 + 0x88: `pos` bytes are read. *)
Definition gcursor (cx : bcx) (W3 : world SEGS) (ms3 : machine_state) (pos : Z) : Prop :=
  0 <= pos <= c_n cx /\
  gslot cx W3 ms3 0x88 (c_p cx + pos) /\ gslot cx W3 ms3 0x90 (c_n cx - pos).

(* The registers every phase of the body keeps: the realigned stack pointer in sp and s1, the caller's stack pointer
   in s0, the shadow offset in s2, the frame's shadow in s8, gp and tp. *)
Definition gregs (cx : bcx) (fp : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (c_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (c_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (c_regs cx) 4 /\
  getr (ms_regs ms3) 18 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 24 = w64 (gSH cx fp).

(* The saved registers of the machine frame, which the epilogue reads back: ra at the caller's sp - 8, then s0, s1,
   s2 .. s11 at sp - 16 - 8j (the registers x8, x9, x18 .. x27). *)
Definition gsaved (cx : bcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).

(* What every phase of the body carries: the pc, the registers, the saved words, the frame's shadow and flag word,
   the frame slots, and the input block kept as the caller gave it. *)
Definition gb_body (cx : bcx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  gregs cx fp ms3 /\ gsaved cx W3 ms3 /\ gshadow cx fp W3 ms3 sh /\ length sh = GB_NSH /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  gslots_fr cx fp W3 ms3 /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)).

(* ---- the table ---- *)

(* The registry r, the call's own 288-byte heap block, and its bytes bs, in the form the callees' contracts state
   them (lib/A/Prog/Check.v, ReacBoxreg*.v). *)
Definition greg (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (r : Z) (bs : list byte) : Prop :=
  In (r, REG_SIZE) (ablocks B ly3 S3) /\ length bs = 288%nat /\
  (forall i, 0 <= i < REG_SIZE ->
     aview SEGS (w_H W3) (ms_mem ms3) (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).
(* The frame's copy `prev` of the table, in the same form (range_free and lowest_free read it there). *)
Definition gprev (cx : bcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (bs : list byte) : Prop :=
  forall i, 0 <= i < REG_SIZE ->
    aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + GO_PREV + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
(* The blocks once the registry is allocated and before it is freed: the caller's, then r. *)
Definition gblk1 (cx : bcx) (ly3 : alayout) (S3 : astate) (r : Z) : Prop :=
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE)].

(* ---- the invariant at each cut ---- *)

(* J, 0x801ec: `i` operations done (0 <= i < 64), `pos` input bytes read; the table r (s4) holds bs, which passes
   Pau's checks (boxreg_inv) for the fabric fab = bx_fabric bs (s9 and slot 0x50); s5 = i. *)
Definition GI_J (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs pos,
  gb_body cx fp GP_J W3 ms3 GSH_J /\ 0 <= i < 64 /\ k <= 1 + 2 * i /\ acc <= GB_A i /\
  gblk1 cx ly3 S3 r /\ greg ly3 S3 W3 ms3 r bs /\ Boxreg.boxreg_inv bs /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 i /\
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) /\
  gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs) /\ gcursor cx W3 ms3 pos.

(* T, the case of op3 = op & 3: op (s6) is read, prev holds a copy of bs, the frame's objects are in scope
   (GSH_it); s10 = r->n = bx_n bs and slot 0x68 = i; for op3 = 0 and 1 also slot 0x48 = bx_n bs. *)
Definition GI_T (op3 i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs pos op,
  gb_body cx fp (GP_T op3) W3 ms3 GSH_it /\ 0 <= i < 64 /\ k <= 1 + 2 * i /\ acc <= GB_A i /\
  gblk1 cx ly3 S3 r /\ greg ly3 S3 W3 ms3 r bs /\ gprev cx fp W3 ms3 bs /\ Boxreg.boxreg_inv bs /\
  0 <= op < 256 /\ Z.land op 3 = op3 /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 22 = w64 op /\
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) /\ getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\
  gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs) /\ gcursor cx W3 ms3 pos /\
  gslot cx W3 ms3 0x68 i /\ (op3 <= 1 -> gslot cx W3 ms3 0x48 (Boxreg.bx_n bs)).

(* K, 0x80ab4: the case is done; prev holds bs (the table before the turn), r holds bs' (after it), both pass
   Pau's checks for the same fabric, bs' keeps what Pau's check_kept asks of bs (llvm_kept, with ren the row
   set_name renamed or -1), and the name the case read is freed; s5 = ren as a 32-bit value. *)
Definition GI_K (i : Z) (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r bs bs' ren pos,
  gb_body cx fp GP_K W3 ms3 GSH_it /\ 0 <= i < 64 /\ k <= 3 + 2 * i /\ acc <= GB_A (i + 1) /\
  gblk1 cx ly3 S3 r /\ greg ly3 S3 W3 ms3 r bs' /\ gprev cx fp W3 ms3 bs /\
  Boxreg.boxreg_inv bs /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs /\
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren /\ -1 <= ren < Boxreg.bx_n bs /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (ren mod 2 ^ 32) /\
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) /\
  gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs) /\ gcursor cx W3 ms3 pos /\
  gslot cx W3 ms3 0x68 i.

(* X, 0x80e14: the loop is done (no input left, or 64 turns); s4 = r, the table, which the exit frees. *)
Definition GI_X (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists r,
  gb_body cx fp GP_X W3 ms3 GSH_J /\ k <= 129 /\ acc <= GB_A 64 /\
  gblk1 cx ly3 S3 r /\ In (r, REG_SIZE) (ablocks B ly3 S3) /\
  getr (ms_regs ms3) 20 = w64 r.

(* ---- a phase ---- *)
(* `gb_from POST GI` says: from any machine state that `GI` describes, the run reaches the entry function's
   post-condition. A phase lemma has the shape `gb_from POST GI_next -> gb_from POST GI_self`; the loop is
   composed by induction on the turns left (BoxLibX.v). *)
Definition gb_from (POST : bcx -> world SEGS -> config -> Prop)
  (GI : bcx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : bcx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  gb_base cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GI cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* The whole call: from the function's first slot under `gb_base` to the same post-condition. The entry phase proves
   it from the loop head. *)
Definition gb_start (POST : bcx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : bcx, gb_base cx ->
  SRr SEGS (c_W cx)
    (mkCfg (mkst (c_regs cx) (w64 (BASE + GP_entry)) (c_mem cx) (seg_rom SEGS)) (c_md cx))
    (POST cx).

(* The post-condition of the whole call, in the shape `apost_base` gives: the machine is back at the caller's return
   address, the journal holds, the callee-saved registers are kept, a0 is 0, the blocks are a permutation of the
   caller's and the caller's input bytes are unchanged. *)
Definition gb_post (cx : bcx) : world SEGS -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = mkCfg (mkst regs' (getr (c_regs cx) 1) mem' (seg_rom SEGS)) md' /\
    ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [] ly' S' W' mem' md' k /\ k <= GB_EV /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
    mo_le MT (c_S cx) S' (c_T cx) /\
    (forall i, 0 <= i < c_n cx ->
       aview SEGS (w_H W') mem' (c_p cx + i) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + i)).

End c.
End b.
End a.

(* ---- the FP state across the snprintf wrapper ----
   reac_boxreg_declare and reac_boxreg_set_name return at SOME FP state fx' (BoxBase.v apost_baseF, pa 82db7cf8c7c):
   its f registers are the entry's except f10, and its fcsr is the entry's or has rounding mode 0. lx_fxr is that
   relation (the B twin's BoxBLxDefs.v name and text); it is reflexive and transitive. A cut is always taken at the
   fx of the Section it is used in, and gb_from is POST-generic; a phase that calls declare / set_name lands its next
   cut at the fx' the call returns, for one fixed POST:
     forall POST i, (forall fx', lx_fxr fx fx' -> gb_from (fx := fx') B MT POST (NEXT (fx := fx') B MT i)) ->
     gb_from B MT POST (PREV B MT i).
   The loop (BoxLxLoop.v) carries lx_fxr fx0 fx from the entry's fx0, and POST is the entry-relative gb_postF fx0. *)
Definition lx_fxr (fxa fxb : YK11.FPState) : Prop :=
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fxb) k = Sem.reg_get (@fp_regs fxa) k) /\
  (@fp_csr fxb = @fp_csr fxa \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fxb)) 5) 7 = 0).

Lemma lx_fxr_refl : forall fx, lx_fxr fx fx.
Proof. intros fx. split; [intros k _; reflexivity | left; reflexivity]. Qed.

Lemma lx_fxr_trans : forall fxa fxb fxc, lx_fxr fxa fxb -> lx_fxr fxb fxc -> lx_fxr fxa fxc.
Proof.
  intros fxa fxb fxc (R1 & C1) (R2 & C2). split.
  - intros k Hk. rewrite (R2 k Hk). exact (R1 k Hk).
  - destruct C2 as [C2 | C2]; [rewrite C2; exact C1 | right; exact C2].
Qed.

(* Rounding mode 0 of the entry's fcsr is kept along lx_fxr: either disjunct gives it at the later FP state. *)
Lemma lx_fxr_frm0 : forall fxa fxb, lx_fxr fxa fxb ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fxa)) 5) 7 = 0 ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fxb)) 5) 7 = 0.
Proof. intros fxa fxb (_ & [C | C]) H; [rewrite C; exact H | exact C]. Qed.

(* A byte the read-only image holds reads as present through any overlay (YP09.v mbyte: the overlay's byte, else the
   image's): what a C string's NUL word needs past the NUL (SnprintfDef.v asn_rom_str's tail clause). *)
Lemma aview_some_of_rom : forall segs (H : word -> bool) (mem : word -> option byte) a,
  seg_rom segs (Z_to_bv 64 a) <> None -> aview segs H mem a <> None.
Proof.
  intros segs H mem a Hs. unfold aview, mbyte.
  destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
  destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | contradiction].
Qed.

(* The walk's post, relative to the entry's FP state fx0: gb_post at the FP state the call ends with. *)
Section f. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg box_listing}.
Variable fx0 : YK11.FPState.
Variable B : asyms.
Variable MT : ameter_ops.
Definition gb_postF (cx : bcx) : world (@pa_segs _ box_listing PI) -> config -> Prop :=
  fun W' c' => exists fxe : YK11.FPState, lx_fxr fx0 fxe /\ gb_post (fx := fxe) B MT cx W' c'.
Lemma gb_postF_of : forall fx cx W' c',
  lx_fxr fx0 fx -> gb_post (fx := fx) B MT cx W' c' -> gb_postF cx W' c'.
Proof. intros fx cx W' c' HR HP. exists fx. split; [exact HR | exact HP]. Qed.
End f.

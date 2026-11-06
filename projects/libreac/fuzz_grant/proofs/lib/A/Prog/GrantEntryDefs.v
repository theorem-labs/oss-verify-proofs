(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* The walk of fuzz_grant's entry function LLVMFuzzerTestOneInput (0x806b0) on the
   ASan build, cut into phases: the data every phase shares.

   The entry function keeps two frames at once:
   - a machine-stack frame of 288 bytes (`addi sp,sp,-288` at slot 0), which holds ra,
     s0..s11 and, below the 32-byte realignment (`andi sp,sp,-32`, slot 0x40), the
     spill slots the body reads back; s1 holds that realigned stack pointer;
   - a frame on the side stack for frames, class 4 (1024-byte slots), taken by
     `__asan_stack_malloc_4` at slot 0x70; s5, and later s6, holds its address F, and
     the function's own 832 bytes live at F..F+831. Its 104 shadow bytes start at
     SHADOW_OFF + F / 8; the slot's flag address sits at F + 1016.

   One phase = one file; the cut between two phases is semantic (a predicate on the
   machine state, `ge_from` below), never a symbolic state, so that no phase has to
   compute another phase's state. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantModel SlotNeeds_c GrantSlotPlan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the function's stack, its frame on the side stack, and its event budget ---- *)

(* The machine stack the call needs: its own 288-byte frame plus the deepest path
   through the called functions (reac_grant_build_sweep -> reac_ctrl_build_grant_sweep
   -> reac_ctrl_stamp_headamp -> ctrl_lay_block -> reac_box_model_block ->
   build_dt1_single = 2544 bytes in all) plus ESTACK for the runtime's own use. *)
Definition GE_STK : Z := 32768.
Definition GE_EV : Z := 2000.
Definition GE_LIVE : Z := 2 ^ 33.
(* The class of the side-stack frame: `__asan_stack_malloc_4`, 1024-byte slots. *)
Definition GE_CID : Z := 4.
Definition GE_FRAME : Z := 832.
Definition GE_NSH : nat := 104%nat.
(* The driver's static empty buffer, which it passes when the input is empty
   (a Theorem Labs lane's lib/A/ACfn.v `A_EMPTY`). *)
Definition GE_EMPTY : Z := 0x5d71a0.

(* ---- the offsets of the frame's objects, from the shadow stores at 0x80794..0x80938 ---- *)
Definition GO_WAS : Z := 32.      (* uint8_t was_set[48][3]    *)
Definition GO_SET : Z := 240.     (* uint8_t set_to[48][3]     *)
Definition GO_A : Z := 448.       (* struct reac_grant_alloc a *)
Definition GO_POLL : Z := 464.    (* uint8_t poll[34]          *)
Definition GO_LIT : Z := 544.     (* the 4-byte compound literal 12 11 05 00 *)
Definition GO_RAW : Z := 560.     (* struct reac_grant_alloc raw *)
Definition GO_UNSET : Z := 576.   (* uint8_t unset_sent[48][3] *)
Definition GO_CH : Z := 784.
Definition GO_PAR : Z := 800.
Definition GO_VAL : Z := 816.

(* The 104 shadow bytes of the frame as the prologue leaves them: 0xf1 left redzone,
   0xf2 between two objects, 0xf3 right redzone, 0xf8 an object out of scope, and 4
   for the compound literal, which is in scope from the first slot. *)
Definition GSH_entry : list Z :=
  [241;241;241;241] ++ repeat 248 18 ++ repeat 242 8 ++ repeat 248 18 ++ repeat 242 8
  ++ [248;242;248;248;248;248;248;242] ++ repeat 242 4
  ++ [4;242;248;242] ++ repeat 248 18 ++ repeat 242 8
  ++ [248;242;248;242;248;243].

(* `was_set` and `set_to` in scope (the two calls of __asan_memset of the prologue). *)
Definition gsh_set (sh : list Z) (lo : nat) (n : nat) (v : Z) : list Z :=
  firstn lo sh ++ repeat v n ++ skipn (lo + n) sh.
Definition GSH_tables : list Z := gsh_set (gsh_set GSH_entry 4 18 0) 30 18 0.
(* `a` marked usable (0x80e34), then `raw` too (0x812b0), then `unset_sent`, with `raw`
   marked unusable again (0x813bc, 0x814e0..0x81528). *)
Definition GSH_a : list Z := gsh_set GSH_tables 56 1 2.
Definition GSH_raw : list Z := gsh_set GSH_a 70 1 2.
Definition GSH_sched : list Z := gsh_set (gsh_set GSH_a 70 1 248) 72 18 0.

(* ---- the pcs of the phase cuts, as offsets in the listing (address - 0x806b0) ---- *)
Definition GP_entry : Z := 0x0.          (* 0x806b0, the first slot              *)
Definition GP_hdr : Z := 0x294.          (* 0x80944, the frame is set up, the header is read next *)
Definition GP_mallocT : Z := 0x2dc.      (* 0x8098c, malloc of the 460-byte table *)
Definition GP_set0 : Z := 0x2ec.         (* 0x8099c, the table is allocated       *)
Definition GP_set : Z := 0x3f4.          (* 0x80aa4, the head of the set loop     *)
Definition GP_unset0 : Z := 0x620.       (* 0x80cd0, the set loop is done         *)
Definition GP_unset : Z := 0x678.        (* 0x80d28, the head of the unset loop   *)
Definition GP_admit : Z := 0x6e0.        (* 0x80d90, the admission tests          *)
Definition GP_sweep : Z := 0x7a8.        (* 0x80e58, after reac_grant_allocate    *)
Definition GP_raw : Z := 0xbfc.          (* 0x812ac, the hand-built allocation    *)
Definition GP_sched0 : Z := 0xd08.       (* 0x813b8, the sweeps are done and freed *)
Definition GP_sched : Z := 0xf14.        (* 0x815c4, the head of the frame loop   *)
Definition GP_freeT : Z := 0x1118.       (* 0x817c8, free of the table            *)
Definition GP_leave : Z := 0x1208.       (* 0x818b8, the frame is given back      *)
Definition GP_ret : Z := 0x127c.         (* 0x8192c, the `ret`                    *)

(* The call sites whose call trace the wrappers' contracts ask for: the return address of
   each call of the memory-checking runtime's wrapper for malloc, and of its wrapper for
   free, as offsets in the listing. *)
Definition GE_MSITES : list Z := [0x2e4; 0x7e0; 0xc7c].
Definition GE_FSITES : list Z := [0xbf0; 0xd08; 0x1120].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the entry function's context: what the call starts from ---- *)
Record ecx := mkECX {
  c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word;
  c_mem : word -> option byte; c_md : Model;
  c_p : Z;                   (* the caller's input buffer      *)
  c_pl : list byte;          (* its bytes                      *)
  c_sp1 : Z;                 (* the realigned machine stack pointer, s1     *)
  c_E0 : env;                (* the atoms of the entry registers            *)
  c_T : Z                    (* the allocator budget the caller grants      *)
}.
Definition c_n (cx : ecx) : Z := Z.of_nat (length (c_pl cx)).

(* The frame this call owns on the side stack, its flag, and its shadow. *)
Definition gF (cx : ecx) (fp : Z) : Z := frame_addr (c_ly cx) GE_CID fp.
Definition gFL (cx : ecx) (fp : Z) : Z := flag_addr (c_ly cx) GE_CID fp.
Definition gSH (cx : ecx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (gF cx fp).

(* What the call may spend with the allocator: the table, the sweep of an admitted
   box, the sweep the harness builds by hand, and the three frees. *)
Definition GE_A1 : Z := mo_malloc MT 460.
Definition GE_A2 : Z := GE_A1 + mo_malloc MT 8670 + mo_free MT.
Definition GE_A3 : Z := GE_A2 + mo_malloc MT 4352 + mo_free MT.
Definition GE_NEED : Z := GE_A3 + mo_free MT.

(* The call chain this call hands to the functions it calls, as cgif's walk builds it
   (lib/A/ACf5.v:128-131): the caller's frame is on the chain when it fits under the
   layout's top. *)
Definition gch (cx : ecx) : list (Z * Z * Z) :=
  if spZ (c_regs cx) + 16 <? ly_top (c_ly cx)
  then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].

Definition ge_base (cx : ecx) : Prop :=
  afn_pre SEGS B GE_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
  getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
  ((c_n cx = 0 /\ c_p cx = GE_EMPTY) \/
   (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
  garr8 SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  frames (c_S cx) = [] /\
  st_nev (c_S cx) + GE_EV <= EV_MAX /\ blocks_bytes (c_S cx) + GE_LIVE <= LIVE_MAX /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
  c_sp1 cx = 32 * ((spZ (c_regs cx) + -288) / 32) /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
  bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
  ew (c_E0 cx) 32 = w64 SHADOW_OFF /\
  mo_ok MT (c_S cx) (c_T cx) /\
  (forall pcf (regsT : bvmap 5 word),
     (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - BASE) GE_MSITES) \/
     (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - BASE) GE_FSITES) ->
     In (call_trace0 pcf regsT (gch cx)) (as_universe B)) /\
  GE_NEED <= c_T cx.

(* ---- the memory of a phase ---- *)

(* The shadow bytes of the frame. *)
Definition gshadow (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + Z.of_nat i) = Some (nth i sh 0).

(* A byte of the frame. *)
Definition gfb (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + off) = Some v.

(* An array of the frame, as a list of bytes. *)
Definition gfarr (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (off : Z) (l : list byte) : Prop :=
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + off)
        (map (fun b : byte => bv_unsigned b) l).

(* A spill slot of the machine frame: the body reads these back after every call. *)
Definition gslot (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some v.

(* The spill slots the body keeps from the two calls of __asan_memset of the prologue
   on: the frame, its shadow base, the shadow offset, the two arrays the harness keeps
   itself, and the four header fields. *)
Definition gslots_mid (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  gslot cx W3 ms3 16 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 24 (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 48 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms3 56 (gSH cx fp) /\
  gslot cx W3 ms3 136 (gF cx fp + GO_SET) /\
  gslot cx W3 ms3 144 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 152 SHADOW_OFF /\
  gslot cx W3 ms3 176 (gF cx fp).

(* The slots the block at 0x80cd0 adds: the address of every remaining object of the
   frame, and the frame itself a second time. *)
Definition gslots_late (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  gslots_mid cx fp W3 ms3 /\
  gslot cx W3 ms3 8 (gF cx fp + GO_POLL) /\
  gslot cx W3 ms3 32 (gF cx fp) /\
  gslot cx W3 ms3 40 (gF cx fp) /\
  gslot cx W3 ms3 72 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 80 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 104 (gF cx fp + GO_CH) /\
  gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_VAL).

(* The registers every phase of the body keeps: the realigned stack pointer in s1, the
   frame base in s6, the shadow offset where the body last left it, gp and tp. *)
Definition gregs (cx : ecx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (c_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (c_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (c_regs cx) 4.

(* The saved registers of the machine frame, which the epilogue reads back. *)
Definition gsaved (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).

(* What every phase of the body carries: the pc, the registers, the spill slots, the
   input block kept as the caller gave it, and the frame's shadow. *)
Definition ge_body (cx : ecx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  gregs cx ms3 /\ gsaved cx W3 ms3 /\ gshadow cx fp W3 ms3 sh /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + 1016) = Some (gFL cx fp) /\
  length sh = GE_NSH /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)).

(* ---- the model of the input, as fuzz_grant's own plain walk reads it ---- *)
(* `GrantSlotPlan` gives the address-free reading of the input: `header`, `nset`,
   `cells_upto`, `tables_at`, `T_end`, `ws_end`, `st_end`, `sched_rd` and `frames`. A
   phase states its tables through those, so that Pau's proved model lemmas apply. *)
Definition ge_hdr (cx : ecx) : GrantSlotPlan.hdr := GrantSlotPlan.header (c_pl cx).
Definition ge_ok (cx : ecx) : bool := GrantSlotPlan.ok (c_pl cx).

(* The head-amp table the harness allocates: a 460-byte block whose bytes are `T`, the
   list fuzz_grant's own plain walk keeps (lib/Prog/GrantSlotPlan.v). Only the bytes of
   the fields the table's layout names are tracked: the three bytes the layout does not
   name (438, 439 and 451) are padding, and the table's writers give back the fields,
   not the padding. *)
Definition gtab (cx : ecx) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (t : Z) (T : list byte) : Prop :=
  In (t, 460) (ablocks B ly3 S3) /\ 0 < t /\ length T = 460%nat /\
  (forall i, 0 <= i < 460 -> i <> 438 -> i <> 439 -> i <> 451 ->
     aview SEGS (w_H W3) (ms_mem ms3) (t + i) = Some (HeadampModel.tb T i)).

(* The blocks after the table was allocated, and the budget each cut may have used. *)
Definition gblk1 (cx : ecx) (ly3 : alayout) (S3 : astate) (t : Z) : Prop :=
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)].

(* ---- the invariant at each cut ---- *)

(* 0x80944: the frame on the side stack is taken and its shadow marked, and the input is
   shorter than FUZZ_INPUT_MAX; the header is read next. The input pointer is in s2, its
   size in s4, the frame in s3 and s5, its shadow base in s6, the shadow offset in s8. *)
Definition GI_hdr (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ge_body cx fp GP_hdr W3 ms3 GSH_entry /\ k <= 0 /\ acc <= 0 /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (c_p cx) /\ getr (ms_regs ms3) 20 = w64 (c_n cx) /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp) /\ getr (ms_regs ms3) 21 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 24 = w64 SHADOW_OFF /\
  gslot cx W3 ms3 176 (gF cx fp).

(* 0x8098c: the header is read, the table is not allocated yet. The input cursor is in
   s10, the bytes left in s7, the base in s11; the frame is in s3 and s5, its shadow
   base in s6 and the shadow offset in s8. *)
Definition GI_mallocT (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ge_body cx fp GP_mallocT W3 ms3 GSH_entry /\ k <= 0 /\ acc <= 0 /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp) /\ getr (ms_regs ms3) 21 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 24 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 26 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) /\
  getr (ms_regs ms3) 23 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) /\
  getr (ms_regs ms3) 27 = w64 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 16 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 24 (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 176 (gF cx fp).

(* 0x80aa4, the head of the set loop: `i` cells are set, `nset - i` turns are left.
   s4 is the table, s5 the input cursor, s6 the frame, s11 the turns left. *)
Definition GI_set (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (i : nat) (t : Z),
  ge_body cx fp GP_set W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  Z.of_nat i < GrantSlotPlan.nset (c_pl cx) /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (snd (GrantSlotPlan.cells_upto (c_pl cx) i))) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 27 = w64 (GrantSlotPlan.nset (c_pl cx) - Z.of_nat i) /\
  gslot cx W3 ms3 120 (c_n cx - Z.of_nat (snd (GrantSlotPlan.cells_upto (c_pl cx) i))) /\
  gslot cx W3 ms3 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslots_mid cx fp W3 ms3 /\
  (let '(T, ws, st) := GrantSlotPlan.tables_at (c_pl cx) i in
     gtab cx ly3 S3 W3 ms3 t T /\ gfarr cx fp W3 ms3 GO_WAS ws /\ gfarr cx fp W3 ms3 GO_SET st /\
     GrantSlotPlan.Hrel T ws st /\ SlotNeeds_c.I1 T).

(* 0x80cd0: every cell the input names is set. *)
Definition GI_unset0 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_unset0 W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp) /\ getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp) /\
  gslot cx W3 ms3 120 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslots_mid cx fp W3 ms3 /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\ gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x80d90: every unset cell carries the enrolling default; the admission tests follow. *)
Definition GI_admit (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_admit W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\ getr (ms_regs ms3) 20 = w64 t /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 120 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_LIT) /\
  gslots_late cx fp W3 ms3 /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\ gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x80e58: the box is admitted or refused, and `a` holds what reac_grant_allocate left.
   s7 is the base, s10 the width the input asked for, s3 and a0 the answer, s2 the
   address of `a`, s6 the shadow base, s5 the shadow offset, s8 the bytes left. *)
Definition GI_sweep (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_sweep W3 ms3 GSH_a /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\ getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\ getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 23 = w64 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))) /\
  getr (ms_regs ms3) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 25 = w64 (gF cx fp + GO_RAW) /\
  getr (ms_regs ms3) 26 = w64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  getr (ms_regs ms3) 19 = w64 (if GrantSlotPlan.ok (c_pl cx) then 0 else -1) /\
  getr (ms_regs ms3) 10 = w64 (if GrantSlotPlan.ok (c_pl cx) then 0 else -1) /\
  (if GrantSlotPlan.ok (c_pl cx)
   then gfb cx fp W3 ms3 GO_A (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))) /\
        gfb cx fp W3 ms3 (GO_A + 1) (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx)))
   else gfb cx fp W3 ms3 GO_A 0 /\ gfb cx fp W3 ms3 (GO_A + 1) 0) /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 120 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_LIT) /\
  gslots_late cx fp W3 ms3 /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\ gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x812ac: the sweep of the admitted box is built, checked and freed, or the box was
   refused and no sweep was built. What follows is the allocation the harness builds by
   hand (fuzz_grant.c:363-387). s5 is the shadow offset, s6 the frame's shadow base, s8
   the bytes of input left, s9 the address of `raw`, s4 the table. *)
Definition GI_raw (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_raw W3 ms3 GSH_a /\ k <= 3 /\ acc <= GE_A2 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 25 = w64 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_LIT) /\
  gslots_late cx fp W3 ms3 /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x813b8: both sweeps were built, checked and freed; the scheduler is set up next. *)
Definition GI_sched0 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_sched0 W3 ms3 GSH_raw /\ k <= 5 /\ acc <= GE_A3 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 25 = w64 (gF cx fp + GO_RAW) /\
  getr (ms_regs ms3) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  gslots_late cx fp W3 ms3 /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\ gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x815c4, the head of the frame loop: `i` frames are run, the table is what the
   scheduler left, and `unset_sent` counts how often each unset cell went out. *)
Definition GI_sched (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (i : nat) (t : Z),
  ge_body cx fp GP_sched W3 ms3 GSH_sched /\ k <= 5 /\ acc <= GE_A3 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  Z.of_nat i < GrantSlotPlan.frames (c_pl cx) /\
  getr (ms_regs ms3) 18 = w64 (Z.of_nat i - GrantSlotPlan.frames (c_pl cx)) /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (gF cx fp + GO_PAR) /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 23 = w64 47 /\ getr (ms_regs ms3) 24 = w64 1 /\
  getr (ms_regs ms3) 25 = w64 (-8) /\ getr (ms_regs ms3) 27 = w64 2 /\
  (let '(sb, sw, per, fr, pe) := GrantSlotPlan.sched_rd (c_pl cx) in
     gslot cx W3 ms3 96 sb /\ gslot cx W3 ms3 88 (sb + sw) /\
     gslot cx W3 ms3 120 (GrantSlotPlan.sched_flag (c_pl cx))) /\
  gslots_late cx fp W3 ms3 /\
  (let '(T, us) := GrantSlotPlan.sched_at (c_pl cx) t i in
     gtab cx ly3 S3 W3 ms3 t T /\ SlotNeeds_c.I1 T /\ length us = 144%nat /\ gfarr cx fp W3 ms3 GO_UNSET us) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\ gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)).

(* 0x817c8: the frames are run; the table is freed and the frame given back. *)
Definition GI_freeT (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_freeT W3 ms3 GSH_sched /\ k <= 5 /\ acc <= GE_A3 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  gslots_late cx fp W3 ms3.

(* 0x818b8: the frame is about to be given back. Two slots reach it: the early return
   of an input of FUZZ_INPUT_MAX bytes or more, which allocates nothing, and the end of
   the body, which has freed the table. Both hold the frame in s3 and s5 and its shadow
   base in s6, and neither leaves a block of its own. *)
Definition GI_leave (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  (exists sh : list Z, ge_body cx fp GP_leave W3 ms3 sh) /\ k <= 6 /\ acc <= GE_NEED /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp) /\ getr (ms_regs ms3) 21 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp).

(* ---- a phase ---- *)
(* `ge_from POST GI` says: from any machine state that `GI` describes, the run reaches
   the entry function's post-condition. A phase lemma has the shape
   `ge_from POST GI_next -> ge_from POST GI_self`; a loop phase is proved by induction
   on the number of turns left. *)
Definition ge_from (POST : ecx -> world SEGS -> config -> Prop)
  (GI : ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  ge_base cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GI cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* The whole call: from the function's first slot under `ge_base` to the same
   post-condition. The entry phase proves it from the phase that follows it. *)
Definition ge_start (POST : ecx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : ecx, ge_base cx ->
  SRr SEGS (c_W cx)
    (mkCfg (mkst (c_regs cx) (w64 (BASE + GP_entry)) (c_mem cx) (seg_rom SEGS)) (c_md cx))
    (POST cx).

(* The post-condition of the whole call, in the shape `apost_base` gives: the machine is
   back at the caller's return address, the journal holds, the callee-saved registers
   are kept, a0 is 0, the blocks are a permutation of the caller's and the caller's
   input bytes are unchanged. *)
Definition ge_post (cx : ecx) : world SEGS -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = mkCfg (mkst regs' (getr (c_regs cx) 1) mem' (seg_rom SEGS)) md' /\
    ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [] ly' S' W' mem' md' k /\ k <= GE_EV /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
    mo_le MT (c_S cx) S' (c_T cx) /\
    (forall i, 0 <= i < c_n cx ->
       aview SEGS (w_H W') mem' (c_p cx + i) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + i)).

End c.
End b.
End a.

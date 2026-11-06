(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryDefs.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntryDefs.v as it
   stands on a working branch 552860c636687 and on a working branch 5651bf66924 (blob dd53d45a240 on both, with the
   current generation's AB01 1e6f4323d1e; the same bytes the port was first made from). Every definition
   name is image A's, so that the phase files need no
   renaming; every number is image B's own, read from fuzz_grant.asan-ubsan (entry 0x80a3c, 1422 instructions).
   What image B makes different, and the measurement behind it:
   - the phase cuts GP_* are image B's offsets from 0x80a3c, not image A's from 0x806b0;
   - GE_STK, GE_EV, GE_LIVE, GE_EMPTY, GE_MSITES and GE_FSITES are GrantBContracts.v's image-B constants
     STK_LLVMFuzzerTestOneInput, EV_LIB_B, LIVE_LIB_B, A_EMPTY_B (0x5d7fe0, not image A's 0x5d71a0),
     TB_LLVMF_MSITES and TB_LLVMF_FSITES; where image A's text and image B's contract disagree the contract wins;
   - the GI_* name image B's own registers and image B's own spill slots, which differ from image A's;
   - the four GSH_* lists are image B's; the 104 shadow bytes the prologue writes (the 104 `sb` stores to s3 + k at
     0x80b2c..0x80cd0) were rebuilt from image B and are EQUAL to image A's GSH_entry byte for byte, and so are the
     three later lists, from image B's own stores: was_set and set_to marked in scope at 0x80ddc..0x80e20 and
     0x80e38..0x80e7c around the two __asan_memset calls at 0x80e34 and 0x80e90, `a` marked 0x02 at 0x81370
     (`sb a0,56(s3)`), `raw` marked 0x02 at 0x81820 (`sb a0,70(s3)`) and 0xf8 again at 0x81948, and `unset_sent`
     marked in scope at 0x81ac0..0x81b08 around the __asan_memset at 0x81b18. *)
(* The walk of fuzz_grant's entry function LLVMFuzzerTestOneInput (image B 0x80a3c) on
   the ASan+UBSan build, cut into phases: the data every phase shares.

   The entry function keeps two frames at once:
   - a machine-stack frame of 288 bytes (`addi sp,sp,-288` at slot 0), which holds ra,
     s0..s11 and, below the 32-byte realignment (`andi sp,sp,-32` at 0x80a7c), the
     spill slots the body reads back; s1 holds that realigned stack pointer;
   - a frame on the side stack for frames, class 4 (1024-byte slots), taken by
     `__asan_stack_malloc_4` at 0x80ab0; s5 holds its address F, and the function's own
     832 bytes live at F..F+831. Its 104 shadow bytes start at SHADOW_OFF + F / 8; the
     slot's flag address sits at F + 1016.

   One phase = one file; the cut between two phases is semantic (a predicate on the
   machine state, `ge_from` below), never a symbolic state, so that no phase has to
   compute another phase's state. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
(* The walk ENGINE is image-independent and comes from lib.Reusable; the image-DEPENDENT
   layer comes from lib.B.Prog. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantModel SlotNeeds_c GrantSlotPlan.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the function's stack, its frame on the side stack, and its event budget ---- *)

(* The machine stack the call needs, the event budget and the live-bytes budget: image
   B's contract names them (GrantBContracts.v:277-279), so the contract's numbers are
   the ones this walk uses. *)
Definition GE_STK : Z := STK_LLVMFuzzerTestOneInput.
Definition GE_EV : Z := EV_LIB_B.
Definition GE_LIVE : Z := LIVE_LIB_B.
(* The class of the side-stack frame: `__asan_stack_malloc_4`, 1024-byte slots. *)
Definition GE_CID : Z := 4.
Definition GE_FRAME : Z := 832.
Definition GE_NSH : nat := 104%nat.
(* The driver's static empty buffer, which it passes when the input is empty. Image B's
   is 0x5d7fe0 (GrantBContracts.v:273 A_EMPTY_B), NOT image A's 0x5d71a0. *)
Definition GE_EMPTY : Z := A_EMPTY_B.

(* ---- the offsets of the frame's objects, from image B's shadow stores at 0x80b2c..0x80cd0 ---- *)
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

(* The 104 shadow bytes of the frame as image B's prologue leaves them: 0xf1 left
   redzone, 0xf2 between two objects, 0xf3 right redzone, 0xf8 an object out of scope,
   and 4 for the compound literal, which is in scope from the first slot. Rebuilt from
   image B's own 104 `sb` stores to s3 + k at 0x80b2c..0x80cd0 (a0 = -8, a1 = -14,
   a3 = -15 then -13 from 0x80b3c, a2 = 4 from 0x80b20); the list is byte for byte
   image A's. *)
Definition GSH_entry : list Z :=
  [241;241;241;241] ++ repeat 248 18 ++ repeat 242 8 ++ repeat 248 18 ++ repeat 242 8
  ++ [248;242;248;248;248;248;248;242] ++ repeat 242 4
  ++ [4;242;248;242] ++ repeat 248 18 ++ repeat 242 8
  ++ [248;242;248;242;248;243].

(* `was_set` and `set_to` in scope (image B marks them at 0x80ddc..0x80e20 and
   0x80e38..0x80e7c, around the two calls of __asan_memset at 0x80e34 and 0x80e90). *)
Definition gsh_set (sh : list Z) (lo : nat) (n : nat) (v : Z) : list Z :=
  firstn lo sh ++ repeat v n ++ skipn (lo + n) sh.
Definition GSH_tables : list Z := gsh_set (gsh_set GSH_entry 4 18 0) 30 18 0.
(* `a` marked usable (0x81370 `sb a0,56(s3)` with a0 = 2), then `raw` too (0x81820
   `sb a0,70(s3)`), then `unset_sent` (0x81ac0..0x81b08, around the __asan_memset at
   0x81b18), with `raw` marked unusable again (0x81948 `sb a0,70(s3)` with a0 = -8). *)
Definition GSH_a : list Z := gsh_set GSH_tables 56 1 2.
Definition GSH_raw : list Z := gsh_set GSH_a 70 1 2.
Definition GSH_sched : list Z := gsh_set (gsh_set GSH_a 70 1 248) 72 18 0.

(* ---- the pcs of the phase cuts, as offsets in image B's listing (address - 0x80a3c) ---- *)
Definition GP_entry : Z := 0x0.          (* 0x80a3c, the first slot              *)
Definition GP_hdr : Z := 0x2c8.          (* 0x80d04, the frame is set up, the header is read next *)
Definition GP_mallocT : Z := 0x374.      (* 0x80db0, malloc of the 460-byte table *)
Definition GP_set0 : Z := 0x384.         (* 0x80dc0, the table is allocated       *)
Definition GP_set : Z := 0x4bc.          (* 0x80ef8, the head of the set loop     *)
Definition GP_unset0 : Z := 0x7e8.       (* 0x81224, the set loop is done         *)
Definition GP_unset : Z := 0x844.        (* 0x81280, the head of the unset loop   *)
Definition GP_admit : Z := 0x8c4.        (* 0x81300, the admission tests          *)
Definition GP_sweep : Z := 0x954.        (* 0x81390, after reac_grant_allocate    *)
Definition GP_raw : Z := 0xde0.          (* 0x8181c, the hand-built allocation    *)
Definition GP_sched0 : Z := 0xf08.       (* 0x81944, the sweeps are done and freed *)
Definition GP_sched : Z := 0x1174.       (* 0x81bb0, the head of the frame loop   *)
Definition GP_freeT : Z := 0x1368.       (* 0x81da4, free of the table            *)
Definition GP_leave : Z := 0x29c.        (* 0x80cd8, the frame is given back; image B puts the release block BEFORE the body *)
Definition GP_ret : Z := 0x358.          (* 0x80d94, the `ret`                   *)

(* The call sites whose call trace the wrappers' contracts ask for: the return address
   of each call of the memory-checking runtime's wrapper for malloc (0x80db4, 0x813d0,
   0x818b4) and of its wrapper for free (0x81808, 0x81940, 0x81da8), as offsets in
   image B's listing. GrantBContracts.v:284-285 states them, and
   AF_LLVMFuzzerTestOneInput = 0 (GrantList.v:11), so the contract's offsets from the
   function's first slot and these offsets from the listing's base are the same. *)
Definition GE_MSITES : list Z := TB_LLVMF_MSITES.
Definition GE_FSITES : list Z := TB_LLVMF_FSITES.

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

(* What the call may spend with the allocator: the table (460 bytes, `li a0,460` at
   0x80db0), the sweep of an admitted box (rows * 34 bytes, `mul a0,s4,34` at 0x813cc,
   at most 255 * 34 = 8670), the sweep the harness builds by hand (4352 bytes,
   `li a0,17; slli a0,a0,8` at 0x818ac), and the three frees. *)
Definition GE_A1 : Z := mo_malloc MT 460.
Definition GE_A2 : Z := GE_A1 + mo_malloc MT 8670 + mo_free MT.
Definition GE_A3 : Z := GE_A2 + mo_malloc MT 4352 + mo_free MT.
Definition GE_NEED : Z := GE_A3 + mo_free MT.

(* The call chain this call hands to the functions it calls, as cgif's walk builds it
   (lib/A/ACf5.v:128-131) and as image B's contract states it
   (GrantBContracts.v:1901): the caller's frame is on the chain when it fits under the
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

(* NOTE on image A's `gslots_mid` and `gslots_late`: they are image A's slot maps and
   are NOT defined here. Image B reuses slots 112 and 120 for different values before
   and after the block at 0x81224..0x81270 (the set loop reads the bitwise complements
   of &was_set and &set_to there; the block then overwrites them with &param and &a),
   so no single shared slot map is true of both halves of the body. Every cut below
   names its own slots, measured. Image B's map after the block is: 0 = h_rows,
   8 = F, 16 = F+GO_RAW, 24 = 256*(h_u16/256), 32 = h_in, 40 = F+GO_UNSET,
   48 = the cursor, 56 = F+GO_LIT, 64 = F+GO_CH, 72 = F, 80 = F+GO_POLL, 88 = h_base,
   96 = F+GO_VAL, 104 = the bytes left, 112 = F+GO_PAR, 120 = F+GO_A, 128 = F+GO_SET,
   136 = F+GO_WAS, 144 = SHADOW_OFF, 152 = t. Slot 176 holds F (0x80ae4) but image B
   never reads it again, so no cut after GP_mallocT carries it. *)

(* The registers every phase of the body keeps: the realigned stack pointer in sp and
   s1, the caller's stack pointer in s0, gp and tp. *)
Definition gregs (cx : ecx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (c_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (c_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (c_regs cx) 4.

(* The saved registers of the machine frame, which the epilogue reads back: image B
   writes ra at sp - 8 (`sd ra,280(sp)` at 0x80a44) and s0..s11 at sp - 16 - 8j
   (0x80a48..0x80a74), the same places as image A. *)
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
   phase states its tables through those, so that Pau's proved model lemmas apply. The
   model is image-independent, so image B uses it unchanged. *)
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
(* Every register number and every slot offset below is image B's own, measured from
   fuzz_grant.asan-ubsan; image A's are different and are named in each comment. *)

(* 0x80d04: the frame on the side stack is taken and its shadow marked, and the input is
   shorter than FUZZ_INPUT_MAX; the header is read next. Image B holds the input
   pointer in s2, its size in s4, the frame's SHADOW base in s3 (`srli s3,a1,3` at
   0x80af8 plus SHADOW_OFF at 0x80b28) and the frame itself in s5; it keeps the frame
   in slot 72 (`sd a6,72(s1)` at 0x80d00) and in slot 176 (0x80ae4), and SHADOW_OFF in
   slot 144 (0x80aa0). Image A instead held the frame in s3 and s5, its shadow base in
   s6 and the shadow offset in s8. *)
Definition GI_hdr (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ge_body cx fp GP_hdr W3 ms3 GSH_entry /\ k <= 0 /\ acc <= 0 /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (c_p cx) /\ getr (ms_regs ms3) 20 = w64 (c_n cx) /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 21 = w64 (gF cx fp) /\
  gslot cx W3 ms3 72 (gF cx fp) /\ gslot cx W3 ms3 144 SHADOW_OFF /\
  gslot cx W3 ms3 176 (gF cx fp).

(* 0x80db0: the header is read, the table is not allocated yet. Image B holds the input
   cursor in s8, the bytes left in s7, the rows in s6 and the `in` field in s9, and
   keeps the base in slot 88 (`sd a0,88(s1)` 0x811d4) and the HIGH BYTE of the 16-bit
   field in slot 24 (`sd a4,24(s1)` at 0x811d8 stores b1 << 8, NOT h_u16; image A
   stored the whole u16 at its slot 24). Image A held the cursor in s10, the bytes left
   in s7 and the base in s11, and kept h_rows in slot 16 and the base in slot 48. *)
Definition GI_mallocT (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ge_body cx fp GP_mallocT W3 ms3 GSH_entry /\ k <= 0 /\ acc <= 0 /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 21 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 24 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) /\
  getr (ms_regs ms3) 23 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) /\
  getr (ms_regs ms3) 22 = w64 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  getr (ms_regs ms3) 25 = w64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 88 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms3 24 (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)) /\
  gslot cx W3 ms3 72 (gF cx fp) /\ gslot cx W3 ms3 144 SHADOW_OFF /\
  gslot cx W3 ms3 176 (gF cx fp).

(* 0x80ef8, the head of the set loop: `i` cells are set, `nset - i` turns are left.
   Image B holds the shadow base in s3, the table in s4, the turns left in s5 (it
   counts DOWN: `addiw s5,s5,-1` at 0x81140, `beqz s5` at 0x81148), the input cursor in
   s7, the bytes left in a2 and the constant 1 in a3 (0x80ef0 and 0x81144). Image A
   held the table in s4, the cursor in s5, the frame in s6 and the turns left in s11.
   Slots 120 and 112 hold the bitwise complements of &was_set and &set_to, which the
   loop's two UBSan pointer-overflow guards read (0x810c8 and 0x81108); the block at
   0x81224 later overwrites both, so they belong to this cut only. *)
Definition GI_set (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (i : nat) (t : Z),
  ge_body cx fp GP_set W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  Z.of_nat i < GrantSlotPlan.nset (c_pl cx) /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (GrantSlotPlan.nset (c_pl cx) - Z.of_nat i) /\
  getr (ms_regs ms3) 23 = w64 (c_p cx + Z.of_nat (snd (GrantSlotPlan.cells_upto (c_pl cx) i))) /\
  getr (ms_regs ms3) 12 = w64 (c_n cx - Z.of_nat (snd (GrantSlotPlan.cells_upto (c_pl cx) i))) /\
  getr (ms_regs ms3) 13 = w64 1 /\
  gslot cx W3 ms3 0 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\
  gslot cx W3 ms3 24 (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)) /\
  gslot cx W3 ms3 32 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 88 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms3 112 (2 ^ 64 - 1 - (gF cx fp + GO_SET)) /\
  gslot cx W3 ms3 120 (2 ^ 64 - 1 - (gF cx fp + GO_WAS)) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  (let '(T, ws, st) := GrantSlotPlan.tables_at (c_pl cx) i in
     gtab cx ly3 S3 W3 ms3 t T /\ gfarr cx fp W3 ms3 GO_WAS ws /\ gfarr cx fp W3 ms3 GO_SET st /\
     GrantSlotPlan.Hrel T ws st /\ SlotNeeds_c.I1 T).

(* 0x81224: every cell the input names is set. Image B holds the end cursor in s7 and
   the bytes left in a2 on all three entry paths (0x81190, 0x81220 and the set loop's
   exit at 0x81148); image A held the cursor in s5 and the bytes left in slot 120.
   Slots 112 and 120 are NOT written on the paths that reach this cut, so they are not
   carried; slot 176 is never read again on image B, so no cut from here on carries it. *)
Definition GI_unset0 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_unset0 W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 12 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 23 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 0 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\
  gslot cx W3 ms3 24 (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)) /\
  gslot cx W3 ms3 32 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 88 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) /\
  SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x81300: every unset cell carries the enrolling default; the admission tests follow.
   The block at 0x81224..0x81270 has written the address of every remaining object of
   the frame, so all twenty slots hold, and each is read on some later path. Image B
   keeps the frame's shadow base in s3 across the whole body and never reloads it;
   image A reloaded it from its slot 56 into s6. *)
Definition GI_admit (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_admit W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  gslot cx W3 ms3 0 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 16 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 24 (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)) /\
  gslot cx W3 ms3 32 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 56 (gF cx fp + GO_LIT) /\ gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\
  gslot cx W3 ms3 72 (gF cx fp) /\ gslot cx W3 ms3 80 (gF cx fp + GO_POLL) /\
  gslot cx W3 ms3 88 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\
  gslot cx W3 ms3 104 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\ gslot cx W3 ms3 120 (gF cx fp + GO_A) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) /\
  SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x81390 (`lbu a1,0(s8)`, which comes BEFORE the split `beq a0,zero,0x813b0` at
   0x81394, so the refused run crosses this cut too): the box is admitted or refused,
   and `a` holds what reac_grant_allocate left. Image B puts the answer in s2 and a0,
   h_base in s4, the cursor in s5, &ch in s6, h_in in s7 and &a in s8, all loaded at
   0x8131c..0x81328 or 0x8134c..0x81358 and not written again before the cut. Registers
   21 and 22 are carried because the REFUSED path (`j 0x8181c` at 0x813ac) reaches
   GP_raw without reloading s5 or s6, and GI_raw needs both. Image A held the answer in
   s3 and a0, the base in s7, the width in s10 and &a in s2. *)
Definition GI_sweep (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_sweep W3 ms3 GSH_a /\ k <= 1 /\ acc <= GE_A1 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 20 = w64 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))) /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  getr (ms_regs ms3) 24 = w64 (gF cx fp + GO_A) /\
  getr (ms_regs ms3) 18 = w64 (if GrantSlotPlan.ok (c_pl cx) then 0 else -1) /\
  getr (ms_regs ms3) 10 = w64 (if GrantSlotPlan.ok (c_pl cx) then 0 else -1) /\
  (if GrantSlotPlan.ok (c_pl cx)
   then gfb cx fp W3 ms3 GO_A (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))) /\
        gfb cx fp W3 ms3 (GO_A + 1) (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx)))
   else gfb cx fp W3 ms3 GO_A 0 /\ gfb cx fp W3 ms3 (GO_A + 1) 0) /\
  gslot cx W3 ms3 0 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 16 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 24 (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)) /\
  gslot cx W3 ms3 32 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 56 (gF cx fp + GO_LIT) /\ gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\
  gslot cx W3 ms3 72 (gF cx fp) /\ gslot cx W3 ms3 80 (gF cx fp + GO_POLL) /\
  gslot cx W3 ms3 88 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\
  gslot cx W3 ms3 104 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\ gslot cx W3 ms3 120 (gF cx fp + GO_A) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) /\
  SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x8181c: the sweep of the admitted box is built, checked and freed, or the box was
   refused and no sweep was built. What follows is the allocation the harness builds by
   hand (fuzz_grant.c:363-387). Both entries (the fall-through 0x8180c..0x81818 and the
   refused path's `j 0x8181c` at 0x813ac) leave the table in s4, the cursor in s5, &ch
   in s6 and the bytes left in s7. Slot 88 cannot be stated here: the admitted path
   overwrote it at 0x81418. Image A held SHADOW_OFF in s5, the shadow base in s6, the
   bytes left in s8 and &raw in s9. *)
Definition GI_raw (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_raw W3 ms3 GSH_a /\ k <= 3 /\ acc <= GE_A2 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 16 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\ gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\ gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x81944: both sweeps were built, checked and freed; the scheduler is set up next.
   s4 is -1 here (`li s4,-1` at 0x81920), so the table is carried in slot 152 only.
   Slot 48 has moved on to the raw cursor (`sd a0,48(s1)` at 0x818a4). *)
Definition GI_sched0 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_sched0 W3 ms3 GSH_raw /\ k <= 5 /\ acc <= GE_A3 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\ gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\ gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  gtab cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x81bb0, the head of the frame loop: `i` frames are run, the table is what the
   scheduler left, and `unset_sent` counts how often each unset cell went out. Image B
   counts the turns UP toward 0 in s5 (`neg s5,a0` at 0x81ba8, `addiw s5,s5,1` at
   0x81d5c, back edge `bnez s5` at 0x81d6c), where image A used s2. Its four loop
   constants are 47 in s2 (0x81b98), 1 in s9 (0x81b70), -1 in s10 (0x81b74), -8 in s8
   (0x81bac) and 2 in s11 (0x81b78); image A had 47 in s7, 1 in s8, -8 in s9 and 2 in
   s11, and no -1. `sched_flag` is in s7 (`and s7,a1,a0` at 0x81b7c), not in a slot.
   Slots 88 and 80 hold the bitwise complements of &was_set and &unset_sent, written at
   0x81b40 and 0x81b60 for the loop's UBSan pointer guards. *)
Definition GI_sched (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (i : nat) (t : Z),
  ge_body cx fp GP_sched W3 ms3 GSH_sched /\ k <= 5 /\ acc <= GE_A3 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  Z.of_nat i < GrantSlotPlan.frames (c_pl cx) /\
  getr (ms_regs ms3) 21 = w64 (Z.of_nat i - GrantSlotPlan.frames (c_pl cx)) /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (GrantSlotPlan.sched_flag (c_pl cx)) /\
  getr (ms_regs ms3) 18 = w64 47 /\ getr (ms_regs ms3) 24 = w64 (-8) /\
  getr (ms_regs ms3) 25 = w64 1 /\ getr (ms_regs ms3) 26 = w64 (-1) /\ getr (ms_regs ms3) 27 = w64 2 /\
  (let '(sb, sw, per, fr, pe) := GrantSlotPlan.sched_rd (c_pl cx) in
     gslot cx W3 ms3 120 sb /\ gslot cx W3 ms3 104 (sb + sw)) /\
  gslot cx W3 ms3 8 (gF cx fp) /\
  gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\
  gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 80 (2 ^ 64 - 1 - (gF cx fp + GO_UNSET)) /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - (gF cx fp + GO_WAS)) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\
  gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  (let '(T, us) := GrantSlotPlan.sched_at (c_pl cx) t i in
     gtab cx ly3 S3 W3 ms3 t T /\ SlotNeeds_c.I1 T /\ length us = 144%nat /\ gfarr cx fp W3 ms3 GO_UNSET us) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)).

(* 0x81da4: the frames are run, or there were none (the setup's `bltu a0,a1` at 0x81b34
   reaches this cut directly), so the scheduler phase has TWO next phases. The table is
   freed and the frame given back. Only s4, s3 and the slots 8 and 72 are read from
   here on (0x81e8c and 0x81e90). *)
Definition GI_freeT (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_freeT W3 ms3 GSH_sched /\ k <= 5 /\ acc <= GE_A3 /\
  gblk1 cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 72 (gF cx fp).

(* 0x80cd8: the frame is about to be given back; image B puts this block BEFORE the
   body. Two paths reach it: the early return of an input of FUZZ_INPUT_MAX bytes or
   more (the fall-through at 0x80cd4), which allocates nothing, and the end of the body
   (`j` at 0x81e94), which has freed the table. Image B holds the frame in a6 and s5
   and its shadow base in s3; image A held the frame in s3 and s5 and its shadow base
   in s6. a6 is CALLER-saved, but no call lies between either entry's write of a6
   (0x80af4 on the early return, `ld a6,72(s1)` at 0x81e90 at the end of the body) and
   its one read at 0x80ce0, so it may stand in this cut; it must NOT stand in GI_freeT,
   which the free call at 0x81da8 crosses. *)
Definition GI_leave (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  (exists sh : list Z, ge_body cx fp GP_leave W3 ms3 sh) /\ k <= 6 /\ acc <= GE_NEED /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
  getr (ms_regs ms3) 16 = w64 (gF cx fp) /\ getr (ms_regs ms3) 21 = w64 (gF cx fp) /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp).

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

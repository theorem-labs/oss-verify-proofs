(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan build: the
   module paths are this unit's, the image is the position-abstract one (pa_segs, BASE + AF_LLVMFuzzerTestOneInput),
   the library shape and every constant of the unit's relocated core are parameters of the Section, and the
   measured needs of this unit's entry (events, live bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput.v; 456 of its 504 lines of code are new or changed and 171 lines of the source are left out. *)
(* The boundary layer of LLVMFuzzerTestOneInput's ASan walk: one state predicate per phase boundary of the
   listing, the statement of each segment lemma, and the composition. The only proof here is the one-line
   allocator-trace lemma llvmf_univ_call; the lanes prove the segments against these statements and the
   boundary owner proves the composition.

   Shape. A boundary is a `world SEGS -> config -> Prop`, as an SRr post-condition is: `acut g pos mf k pc P`
   says the run is at slot pc of the listing, the journal from the entry state g holds with the entry's one
   side-stack frame (4, pos) as its `own`, k events have been counted, and P holds of the state. A segment is
   `forall ..., <start> W2 c2 -> SRr SEGS W2 c2 (<end> ...)`. Addresses are the ASan listing's.

   What a boundary carries: the slot, the journal and its event count, the frame (4, pos) and the machine frame
   mf, the registers the next segment reads, the bytes of the side-stack frame's live variables and of the
   machine frame's two counter slots, the shadow of each live variable, the live heap blocks, and the value each
   holds in the plain model of the harness (lib/Prog/SlotModel.v, RcIdentModel.v, IdentSpec.v), which is a
   function of the input bytes alone.

   These are the boundaries as measured. A lane that finds its segment needs one more fact adds it to the end of
   the segment before it and to the start of its own; nothing else moves. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput.
(* The plain model of the harness: address-free, a function of the input bytes. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The side-stack frame's variables, from the frame description at object 2 (0x13d25). *)
Definition V_before : Z := 32.   Definition N_before : Z := 38.
Definition V_again : Z := 112.   Definition N_again : Z := 38.
Definition V_s : Z := 192.       Definition N_s : Z := 8.
Definition V_v : Z := 224.       Definition N_v : Z := 20.
Definition V_ev : Z := 288.      Definition N_ev : Z := 24.
Definition V_id : Z := 352.      Definition N_id : Z := 38.
Definition V_hw : Z := 432.      Definition N_hw : Z := 12.
Definition V_f : Z := 464.       Definition N_f : Z := 8.
Definition V_ef : Z := 496.      Definition N_ef : Z := 16.
Definition V_nm : Z := 528.      Definition N_nm : Z := 32.
Definition V_dp : Z := 592.      Definition N_dp : Z := 64.
Definition V_w4 : Z := 688.      Definition N_w4 : Z := 8.
Definition V_cnt : Z := 720.     Definition N_cnt : Z := 8.
(* The machine frame's two uninstrumented counter slots (put_dec's `n` argument). *)
Definition M_n1 : Z := 208.      Definition M_n2 : Z := 200.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The same Section the contract is stated in, in the same order (LLVMFuzzerTestOneInput.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

(* ---- the entry state the whole walk is relative to ------------------------------------------------------- *)
Record ectx : Type := mkEctx {
e_ly : alayout; e_S : astate; e_W : world SEGS; e_mem : word -> option byte; e_md : Model;
e_regs : bvmap 5 word; e_p : Z; e_n : Z; e_pl : list byte; e_M : Z }.
Definition e_sp0 (g : ectx) : Z := spZ (e_regs g).
(* The entry's class-4 side-stack frame; frame_addr reads ly_F only, which layout_le keeps (YG0f.v:65,340). *)
Definition SFa (g : ectx) (pos : Z) : Z := frame_addr (e_ly g) 4 pos.

Definition bytes_at8 (W2 : world SEGS) (mem2 : word -> option byte) (a : Z) (bs : list byte) : Prop :=
garr8 SEGS (rd W2 mem2) a (map (fun b : byte => bv_unsigned b) bs).
(* The shadow of a whole range, granule by granule, including a last partial granule: what abcmp_realizes and
   the wrappers ask of a range they read (measured). *)
Definition sh_blk (W2 : world SEGS) (mem2 : word -> option byte) (a n : Z) : Prop :=
block_shadow (aview SEGS (w_H W2) mem2) SHADOW_OFF a n.
Definition sh_zero (W2 : world SEGS) (mem2 : word -> option byte) (a n : Z) : Prop :=
zero_shadow (aview SEGS (w_H W2) mem2) SHADOW_OFF a n.

(* The contract's pre-condition at the entry state, as one name: a fact about g alone, never re-proved. A
   segment that needs the read-only image, the sink, the meta table, the fds/fs or the input block at its own
   state derives it from this and acut's journal (HRO with IdentBase.arodata_ok_journalP; ASINK_NONE_KEPT and
   AMETA_INV_KEPT; AJ_NIL_IO). Measured. *)
Definition e_pre (g : ectx) : Prop :=
tLLVMFuzzerTestOneInput_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS
(e_regs g) (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) (e_pl g) (e_M g).

(* What every boundary after the prologue carries: the machine frame, the frame pointer, the shadow base and the
   shadow address of the frame in their places, the read-only image, the sink and the meta table, and the input
   block the contract gave (the journal keeps its bytes: this walk's FP is empty).
   0x8074c (andi sp,sp,-32), 0x80750 (mv s1,sp), 0x80748 (addi s0,sp,320), 0x80774 (sd a7,176(s1)),
   0x80988 (sd a6,80(s1)), 0x807b8 (sd a6,192(s1)), 0x807c8 + 0x807f4 (s3 = shadow_addr SF). *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition ecommon (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
getr regs2 2 = w64 mf /\ getr regs2 9 = w64 mf /\ getr regs2 8 = w64 (e_sp0 g) /\
e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ mf mod 32 = 0 /\
getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
getr regs2 19 = w64 (shadow_addr (SFa g pos)) /\
val_mem SEGS (rd W2 mem2) (mf + 80) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 192) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 176) 8 SHADOW_OFF /\
(* the entry's own saved return address and frame pointer, for the call chain of every call it makes
   (0x80714 sd ra,312(sp); 0x80718 sd s0,304(sp)) *)
val_mem SEGS (rd W2 mem2) (e_sp0 g - 8) 8 RA_LLVMF /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 16) 8 (s0Z (e_regs g)) /\
(* the eleven other callee-saved words of the prologue, which the epilogue restores (0x8071c..0x80744,
   0x82144..0x8216c; measured) *)
val_mem SEGS (rd W2 mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)) /\
(* the frame pointer's own copy and the frame's flag word, written once in A and read by the release
   (0x80984 sd s4,24(s1); 0x820f8, 0x8211c; measured) *)
val_mem SEGS (rd W2 mem2) (mf + 24) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos) /\
(* The contract's pre-condition of the entry state: it speaks of g alone, so it holds at every boundary
   unchanged, and it is where a segment gets the input block, the allocator invariant and its event and live
   room, the entry's call chain, the read-only image (through HRO and IdentBase's arodata_ok_journalP), the
   sink and the meta table. The post needs the last two at the return: ASINK_NONE_KEPT and AMETA_INV_KEPT give
   them from the journal, so no boundary carries an opaque predicate of the CURRENT state. *)
e_pre g /\
(forall fd, fd_lookup (m_fds md2) fd = fd_lookup (m_fds (e_md g)) fd) /\
m_fs md2 = m_fs (e_md g) /\
bytes_at8 W2 mem2 (e_p g) (e_pl g).

(* A boundary: at slot pc, with the journal from the entry state and the entry's own frame. *)
Definition acut (g : ectx) (pos mf k : Z) (pc : Z)
(P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = cfg_at SEGS pc regs2 mem2 md2 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k /\
frames S2 = [(4, pos)] /\ 0 <= k <= EV_LLVMF /\
(* the meter, event by event: what the run has spent, and what is left. After a program call (whose
   post says nothing of the meter) both follow from the contract's HMT0 (mo_le MT Sc S2 0) with mo_le_trans
   and mo_ok_step. *)
mo_le MT (e_S g) S2 (k * (mo_malloc MT 256 + mo_free MT)) /\
mo_ok MT S2 ((EV_LLVMF - k) * (mo_malloc MT 256 + mo_free MT)) /\
ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 /\
P ly2 S2 W2 regs2 mem2 md2.

(* The heap blocks of the run, as a list; `hblocks` says exactly these are live beyond the entry's. *)
Definition hblocks (g : ectx) (ly2 : alayout) (S2 : astate) (hs : list (Z * Z)) : Prop :=
Permutation (ablocks B ly2 S2) (hs ++ ablocks B (e_ly g) (e_S g)) /\
Forall (fun h => 4096 <= fst h /\ 0 <= snd h) hs.

(* ---- the model of the harness, from the plain files ------------------------------------------------------ *)
(* The identity struct after i records, the hardware block, and the input cursor; SlotModel.v:46,53,61,62,31. *)
Definition m_id (g : ectx) (i : nat) : list byte := SlotModel.rec_id (e_pl g) i.
Definition m_have (g : ectx) (i : nat) : Z := SlotModel.rec_have (e_pl g) i.
Definition m_hwb (g : ectx) (i : nat) : list byte := SlotModel.rec_hwb (e_pl g) i.
Definition m_cur (g : ectx) (i : nat) : Z := SlotModel.rec_c (e_pl g) i.
Definition m_nrec (g : ectx) : nat := SlotModel.nrecn (e_pl g).
(* `id` (38 bytes at SF+352): its bytes, and its shadow as B sets it at 0x80990..0x809a4 (four 0 cells and a
   last cell 6) and nothing re-poisons before L (0x820d8): sh_zero is the four full cells, sh_blk the whole
   object, which __asan_memcpy, reac_identity_ingest, reac_box_family_of (afobj) and reac_box_name (rbn_said)
   ask (measured). *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition id_at (g : ectx) (pos : Z) (i : nat) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
bytes_at8 W2 mem2 (SFa g pos + V_id) (m_id g i) /\ sh_zero W2 mem2 (SFa g pos + V_id) N_id /\
sh_blk W2 mem2 (SFa g pos + V_id) N_id.
(* `hw` (12 bytes at SF+432): have, the eight hw bytes, and its shadow as B sets it at 0x80a68 / 0x80a6c (a 0
   cell and a last cell 4), never re-poisoned before L (0x820dc); seg_E's bcmp at 0x815b8 reads SF+436..443
   (measured). *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition hw_at (g : ectx) (pos : Z) (i : nat) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (SFa g pos + V_hw) 4 (m_have g i) /\
bytes_at8 W2 mem2 (SFa g pos + V_hw + 4) (m_hwb g i) /\ sh_zero W2 mem2 (SFa g pos + V_hw) N_hw /\
sh_blk W2 mem2 (SFa g pos + V_hw) N_hw.
(* The input cursor the loop keeps: x26 = p + c and x18 = n - c (0x80ab4, 0x80ac8, 0x813b4, 0x813bc). *)
Definition cur_at (g : ectx) (i : nat) (regs2 : bvmap 5 word) : Prop :=
getr regs2 26 = w64 (e_p g + m_cur g i) /\ getr regs2 18 = w64 (e_n g - m_cur g i) /\
0 <= m_cur g i <= e_n g.
(* The machine-frame slots the record loop reads, set once at 0x80a88 and 0x80ae8..0x80b1c, after the guard at
   0x80a8c (and all but mf+128 after the guard at 0x80ad4): only rec_live and the record body carry them. *)
Definition mf_fixed (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 32) 8 (SFa g pos + V_v) /\
val_mem SEGS (rd W2 mem2) (mf + 40) 8 (SFa g pos + V_s) /\
val_mem SEGS (rd W2 mem2) (mf + 48) 8 (SFa g pos + V_hw) /\
val_mem SEGS (rd W2 mem2) (mf + 72) 8 (SFa g pos + V_ev) /\
val_mem SEGS (rd W2 mem2) (mf + 88) 8 (SFa g pos + V_before) /\
val_mem SEGS (rd W2 mem2) (mf + 96) 8 (SFa g pos + V_again + 28) /\
val_mem SEGS (rd W2 mem2) (mf + 104) 8 (SFa g pos + V_again + 3) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SFa g pos + V_id + 28) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SFa g pos + V_id + 3).
(* mf+168 holds &again until segment F stores t_out there (0x816ac; measured). *)
Definition mf_again (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SFa g pos + V_again).
(* mf+184 holds &id from 0x809b0 until 0x818bc, where segment I overwrites it with the name buffer. *)
Definition mf_id (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id).
(* mf+48 holds &hw from 0x80a74 (read by seg_E at 0x81584); mf+128 holds &id+3 from 0x80a88 (read by seg_I at
   0x81890 and seg_J at 0x8198c). Both are stored before the two guards, so they reach the loop exit on every
   path; mf_fixed holds both (its third and last conjuncts). *)
Definition mf_hw (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 48) 8 (SFa g pos + V_hw).
Definition mf_id3 (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SFa g pos + V_id + 3).
(* What the record loop carries from one record to the next. *)
Definition rec_live (g : ectx) (pos mf : Z) (i : nat) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.nrec (e_pl g)) /\
mf_fixed g pos mf W2 mem2 /\ cur_at g i regs2 /\
id_at g pos i W2 mem2 /\ hw_at g pos i W2 mem2 /\ hblocks g ly2 S2 [] /\
mf_id g pos mf W2 mem2 /\ mf_again g pos mf W2 mem2.

(* ---- the boundaries ---------------------------------------------------------------------------------------- *)

(* 0x8070c, the entry: the contract's pre-condition, before the frame exists. *)
Definition inv_entry (g : ectx) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = e_W g /\ c2 = cfg_at SEGS A_LLVMFuzzerTestOneInputP (e_regs g) (e_mem g) (e_md g).

(* 0x8098c, A -> B: the class-4 frame is taken, its description words and the flag word are written, and every
   variable's shadow is poisoned; the machine frame holds the frame pointer (0x80984 sd s4,24(s1)) and the frame
   address (0x80988 sd a6,80(s1)), which ecommon states, and a6 still holds the frame address B reads at
   0x8098c (measured). (0x80780 stack_malloc_4; 0x807e4..0x807ec the three description words;
   0x807f8..0x80978 the shadow; 0x8097c the size >= 2^26 exit, refuted by e_pre.) *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition inv_A_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf 0 (BASE + 0x280)
(fun ly2 S2 W2 regs2 mem2 md2 =>
val_mem SEGS (rd W2 mem2) (SFa g pos) 8 0x41b58ab3 /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 8) 8 (VAL (A_OBJ 2)) /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 16) 8 (VAL (A_OBJ 3)) /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 1016) 8 (flag_addr ly2 4 pos) /\
hblocks g ly2 S2 [] /\
getr regs2 16 = w64 (SFa g pos) /\
getr regs2 18 = w64 (e_n g) /\ getr regs2 26 = w64 (e_p g)).

(* 0x80a7c, B -> C: the slot of the __asan_memset call that clears `hw`. The eight start-up checks passed; `id`
   holds ID0 (SlotModel rec_id _ 0) and the pointer to it is in mf+184 (0x809b0). The memset's arguments are in
   place (0x80a5c..0x80a78), `hw`'s two shadow bytes are set (0x80a68 0, 0x80a6c 4), and the cursor registers
   still hold the input block (measured). *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition inv_B_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf 0 (BASE + 0x370)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos 0 W2 mem2 /\ hblocks g ly2 S2 [] /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id) /\
val_mem SEGS (rd W2 mem2) (mf + 48) 8 (SFa g pos + V_hw) /\
getr regs2 10 = w64 (SFa g pos + V_hw) /\ getr regs2 11 = w64 0 /\ getr regs2 12 = w64 12 /\
getr regs2 18 = w64 (e_n g) /\ getr regs2 26 = w64 (e_p g) /\
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 /\
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4).

(* 0x80b20, the record loop's head after i records. The loop is rotated: 0x80b20 is reached only with
   i < nrec (the guards 0x80a8c and 0x80ad4 and the test 0x81400 bne), so inv_rec carries i < nrec.
   The index is x20 (0x80ad8 li s4,0; 0x813f4 addiw s4,s5,1), the cursor x26 / x18, nrec at mf+112
   (0x80ad0); x21 = 6 and x24 = SF+32 (0x80b04, 0x80adc). Measured. *)
Definition inv_rec (g : ectx) (pos mf : Z) (i : nat) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i) (BASE + 0x414)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\ getr regs2 20 = w64 (Z.of_nat i) /\
getr regs2 21 = w64 6 /\ getr regs2 24 = w64 (SFa g pos + V_before) /\
rec_live g pos mf i ly2 S2 W2 regs2 mem2).

(* 0x8157c, the loop's exit (both guards and the loop test jump here). On the two guard paths (0x80a8c with
   n = 0, 0x80ad4 with nrec = 0) only mf+48 (0x80a74), mf+128 (0x80a88) and mf+184 (0x809b0) of the machine
   frame's pointer slots are stored, and mf+112 only on the second, so this boundary carries those three and
   nothing of mf_fixed / mf_again. 0x8157c reads mf+184, 0x81584 reads mf+48. *)
Definition inv_exit (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g)) (BASE + 0xe70)
(fun ly2 S2 W2 regs2 mem2 md2 =>
cur_at g (m_nrec g) regs2 /\ id_at g pos (m_nrec g) W2 mem2 /\ hw_at g pos (m_nrec g) W2 mem2 /\
hblocks g ly2 S2 [] /\ mf_hw g pos mf W2 mem2 /\ mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2).

(* ---- the record body ------------------------------------------------------------------------------------- *)
(* What the switch, the four cases and the join share (measured). `pl` is the payload copy made at
   0x80bc8; the guard copy made at 0x80c40 is freed at 0x80cd4, before the first case boundary. *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition P_body (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
(ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
(i < m_nrec g)%nat /\ hblocks g ly2 S2 [(pl, SlotModel.rec_k (e_pl g) i)] /\
bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) /\
id_at g pos (S i) W2 mem2 /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.nrec (e_pl g)) /\ mf_fixed g pos mf W2 mem2 /\
mf_id g pos mf W2 mem2 /\ mf_again g pos mf W2 mem2 /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (e_p g + SlotModel.rec_body (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (e_n g - SlotModel.rec_body (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 pl /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (Z.of_nat i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
0 <= m_cur g (S i) <= e_n g.

(* 0x80d04, D1 -> D2: both copies are made, both ingest calls have run, the guard copy is freed, and the third
   same_id compare has passed (0x80cfc beq -> 0x80d04). Registers measured: x27 the record's address,
   x22 its length, x23 the ingest result, x25 the `again` struct's has_fw byte. *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan; x23 = ingest result by HING (a callee's result, unchecked) *)
Definition inv_D1_end (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0x5f8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_at g pos i W2 mem2 /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
sh_blk W2 mem2 (SFa g pos + V_again) N_again /\
getr regs2 21 = w64 (RcIdentModel.fw_milli (m_id g (S i))) /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
bytes_at8 W2 mem2 (SFa g pos + V_again) (m_id g (S i)) /\
getr regs2 27 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 23 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 25 = w64 (RcIdentModel.bz (RcIdentModel.nthb (m_id g (S i)) 2))).

(* The four exits of the switch (measured): the version case at 0x80f20, the model-name case at 0x81170,
   the firmware case at 0x81208, and the ignored-record path, which goes straight to the join at 0x813b4. *)
Definition inv_caseV (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0x814)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\
hw_at g pos i W2 mem2 /\
SlotModel.rec_r (e_pl g) i = 1 /\ SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_REAC_VERSION /\
getr regs2 25 = w64 pl /\ getr regs2 14 = w64 SHADOW_OFF /\
getr regs2 10 = w64 (pl + 2) /\ getr regs2 11 = w64 (shadow_addr (pl + 2)) /\
getr regs2 18 = w64 (RcIdentModel.major (m_id g (S i))) /\
getr regs2 26 = w64 (RcIdentModel.minor (m_id g (S i))) /\
getr regs2 24 = w64 (RcIdentModel.patch (m_id g (S i))) /\
getr regs2 20 = w64 (SFa g pos + V_ev)).
Definition inv_caseM (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0xa64)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\
hw_at g pos (S i) W2 mem2 /\
SlotModel.rec_r (e_pl g) i = 1 /\ SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_MODEL_NAME /\
getr regs2 20 = w64 (RcIdentModel.has_model_name (m_id g (S i)))).
Definition inv_caseF (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0xafc)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\
hw_at g pos (S i) W2 mem2 /\
SlotModel.rec_r (e_pl g) i = 1 /\ SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_FIRMWARE /\
getr regs2 21 = w64 (RcIdentModel.fw_milli (m_id g (S i))) /\ getr regs2 25 = w64 pl /\
getr regs2 15 = w64 SHADOW_OFF /\ getr regs2 20 = w64 (SFa g pos + V_s)).
(* 0x813b4, the join every case reaches: the record's tail, before the cursor advance. The four cases reload
   x26, x24, x25, x21 from mf+136, mf+88, mf+152, mf+160 before it (measured). *)
Definition inv_tail (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0xca8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_at g pos (S i) W2 mem2 /\
getr regs2 26 = w64 (e_p g + SlotModel.rec_body (e_pl g) i) /\
getr regs2 24 = w64 (SFa g pos + V_before) /\
getr regs2 25 = w64 pl /\ getr regs2 21 = w64 (Z.of_nat i)).

(* 0x81400, the loop test: the payload copy is freed, the cursor has moved on one record, and the index is
   i + 1 in x20 with nrec in x10 (0x813f4, 0x813f8). *)
Definition inv_D6_end (g : ectx) (pos mf : Z) (i : nat) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 4) (BASE + 0xcf4)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\ getr regs2 20 = w64 (Z.of_nat (S i)) /\
getr regs2 10 = w64 (SlotModel.nrec (e_pl g)) /\ getr regs2 21 = w64 6 /\
getr regs2 24 = w64 (SFa g pos + V_before) /\
rec_live g pos mf (S i) ly2 S2 W2 regs2 mem2).

(* 0x815f8, E -> F: reac_box_family_of agrees with the harness's own table (the inlined family_of_hw loop at
   0x815ac), and the cursor is at the tail. Both paths in (0x815d0 beqz s6 with no row matched, and 0x815f4
   falling through) store nothing in the machine frame; after E nothing reads mf+48 again. *)
Definition inv_E_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g)) (BASE + 0xeec)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hw_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
SlotModel.FAM (SlotModel.idT (e_pl g)) =
SlotModel.fam_hw (m_have g (m_nrec g)) (m_hwb g (m_nrec g)) /\
getr regs2 26 = w64 (e_p g + SlotModel.cT (e_pl g)) /\
getr regs2 18 = w64 (e_n g - SlotModel.cT (e_pl g)) /\
getr regs2 13 = w64 SHADOW_OFF).

(* 0x816e4, F -> G: the ten tail bytes are in registers and in four machine-frame slots (measured;
   0x815f8..0x816e0). The boundary is the slot of the first malloc. *)
Definition inv_F_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g)) (BASE + 0xfd8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hw_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
getr regs2 10 = w64 (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) /\
getr regs2 20 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
getr regs2 25 = w64 (SlotModel.t_cap_ver (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 24 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 23 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
getr regs2 21 = w64 (SlotModel.tb (e_pl g) 9) /\
getr regs2 18 = w64 (SlotModel.tb (e_pl g) 10) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g))).

(* 0x817bc, G -> H: the slot of put_dec's first call into `ef`. The two capacity-chosen heap buffers were made,
   used by the formatters and freed; `f` and `ef` are unpoisoned (0x81784..0x8178c), the counter slot is 0
   (0x81790), and put_dec's arguments are in place: a0 = x20 = SF+496, a1 = mf+208, a2 = x18 = fw / 1000
   (0x81794..0x817a8: ((fw mod 2^16) >> 3) * 8389 >> 20, equal to fw / 1000 for every fw < 2^16), a3 = 1; x21
   = fw (0x816fc). x23 / x24 / x26 and the four tail slots pass through to I, J and K; H reads mf+184
   (0x8187c) and I reads mf+128 (0x81890). Measured. *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition inv_G_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x10b0)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
sh_zero W2 mem2 (SFa g pos + V_f) N_f /\ sh_zero W2 mem2 (SFa g pos + V_ef) N_ef /\
val_mem SEGS (rd W2 mem2) (mf + M_n1) 8 0 /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) /\
getr regs2 10 = w64 (SFa g pos + V_ef) /\ getr regs2 20 = w64 (SFa g pos + V_ef) /\
getr regs2 11 = w64 (mf + M_n1) /\ getr regs2 13 = w64 1 /\
getr regs2 12 = w64 (SlotModel.t_any_fw (e_pl g) / 1000) /\
getr regs2 18 = w64 (SlotModel.t_any_fw (e_pl g) / 1000) /\
getr regs2 21 = w64 (SlotModel.t_any_fw (e_pl g)) /\
getr regs2 23 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
getr regs2 24 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g))).

(* 0x81878, H -> I: the slot of `bltz a1` that picks the family source (t_fam_raw >= 128 jumps to 0x8188c, so
   0x81880 is not on every path; checked on fuzz_identity.asan). The "any firmware value" block is done: ef holds the
   expected string, the formatter's output in `f` equals it (the bcmp at 0x8185c), and f / ef are re-poisoned
   (0x8186c..0x81874). a1 = t_fam_raw << 56 (0x81868); x27 = cap_disp (0x81824). I reads x23, x24, x26, x27,
   mf+128 (0x81890), mf+184 (0x8187c, 0x818a0), mf+160 / mf+168; J and K read mf+136 / mf+144. *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan *)
Definition inv_H_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x116c)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
bytes_at8 W2 mem2 (SFa g pos + V_ef) (SlotModel.t_EF (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) /\
getr regs2 11 = w64 (SlotModel.t_fam_raw (e_pl g) * 2 ^ 56) /\
getr regs2 23 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
getr regs2 24 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.t_cap_disp (e_pl g))).

(* 0x81974, I -> J: the family and its stem are taken, the three output buffers are made (nm at mf+184, 0x818bc;
   tk in x21, dp in x22), and the two reac_box_name calls have run (the refusing one at 0x81930, the real one at
   0x8196c, whose result is in a0: 0x81974 `mv s11,a0` has not run). x25 = the family (0x81884 / 0x8188c),
   x23 = id's has_model_name byte (0x818a4), x24 = t_in (0x818ec), x26 = t_out (0x818d4), x20 = cap_tok
   (0x818c4), mf+152 = cap_name (0x818b0). J reads mf+128 (0x8198c), mf+144 / 152 / 160 / 168; K reads mf+136.
   Measured on fuzz_identity.asan. *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan; x10 = r by HBN, x25 = family by HFAM (callees' results, unchecked) *)
Definition inv_I_end (g : ectx) (pos mf : Z) (nm tk dp : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1268)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ mf_id3 g pos mf W2 mem2 /\
hblocks g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
getr regs2 10 = w64 (SlotModel.n_r (e_pl g)) /\
getr regs2 25 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 23 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
getr regs2 24 = w64 (SlotModel.t_in (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_out (e_pl g)) /\
getr regs2 20 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 21 = w64 tk /\ getr regs2 22 = w64 dp /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 (SlotModel.t_cap_name (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g)) /\
(SlotModel.n_r (e_pl g) = 0 ->
bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0]))).

(* 0x81e60, J -> K, the path with good widths (n_wok = true): the expected name and display are built in the
   frame (exp_nm at x26 = SF+528, exp_dp at x24 = SF+592; their shadow zeroed at 0x819f4..0x81a20), and the
   fits case is decided. With bad widths the run goes 0x81a2c -> 0x81e68 -> 0x82090 (r = -1), which seg_J
   ends at inv_K_end. K reads x27 (0x81e68), x20 / x21 / x22 (0x81e88..0x81eac), x26 / x24 (0x81ebc, 0x81ecc),
   mf+184 / 152 / 144 / 160 / 168 / 136. Measured on fuzz_identity.asan. *)
(* not covered by entrycheck: hand-checked against fuzz_identity.asan; x27 = r by HBN (a callee's result, unchecked) *)
Definition inv_J_end (g : ectx) (pos mf : Z) (nm tk dp : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1754)
(fun ly2 S2 W2 regs2 mem2 md2 =>
hblocks g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
SlotModel.n_wok (e_pl g) = true /\
getr regs2 27 = w64 (SlotModel.n_r (e_pl g)) /\
getr regs2 26 = w64 (SFa g pos + V_nm) /\ getr regs2 24 = w64 (SFa g pos + V_dp) /\
getr regs2 20 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 21 = w64 tk /\ getr regs2 22 = w64 dp /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 (SlotModel.t_cap_name (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g)) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0]) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
(SlotModel.n_r (e_pl g) = 0 ->
bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0]))).

(* 0x82090, K -> L: every check of the r = 0 branch passed (the three strlen / check_str pairs, the two strcmp
   of name and display, the token loop, reac_box_catalogue and the two reac_box_catalogue_defect calls). *)
Definition inv_K_end (g : ectx) (pos mf : Z) (nm tk dp : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1984)
(fun ly2 S2 W2 regs2 mem2 md2 =>
hblocks g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
getr regs2 22 = w64 dp /\ getr regs2 21 = w64 tk /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm).

(* The return: the contract's post-condition at RA_LLVMF. L frees the three buffers, releases the frame
   (shadow 0xf5 and the flag byte) and returns 0. *)
Definition inv_ret (g : ectx) (l : lleaf) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k,
c2 = cfg_at SEGS RA_LLVMF regs2 mem2 md2 /\
tLLVMFuzzerTestOneInput_post B MT XN_LIB LLVMF_STK EV_LIB asink_syms_T KS asink_none ameta_inv
(e_regs g) (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) (e_M g) l
ly2 S2 W2 regs2 mem2 md2 k.

(* ---- the allocator call traces ---------------------------------------------------------------------------- *)
(* amalloc04_rule and afree04_rule ask `In (call_trace0 pc0 regsT ch) (as_universe B)` of each call. A segment
   states the contract's HUMM / HUMF (LLVMFuzzerTestOneInput.v, over LLVMF_MALLOC_CTX / LLVMF_FREE_CTX) as its
   own Hypotheses, with the contract's text. At a call whose return address is BASE + o, chain_pre gives either
   the entry's one frame record (fp, RA_LLVMF, v) (the entry is entered with ch = []) or, when bad_next holds at
   sp0, no record (measured): `llvmf_univ_call _ _ _ _ _ HUMM` with
   `In [raZ regsT; RA_LLVMF] LLVMF_MALLOC_CTX`, or `llvmf_univ_call0 _ _ _ HUMM` with
   `In [raZ regsT] LLVMF_MALLOC_CTX` (HUMF and LLVMF_FREE_CTX for free). *)
Lemma llvmf_univ_call : forall (pc0 : Z) (CTX : list (list Z)) (regsT : bvmap 5 word) (fp v : Z),
(forall c, In c CTX ->
 In (firstn kUnwindMax (pc0 :: flat_map (fun r => if r =? pc0 then [] else [r]) c)) (as_universe B)) ->
In [raZ regsT; RA_LLVMF] CTX ->
In (call_trace0 pc0 regsT [(fp, RA_LLVMF, v)]) (as_universe B).
Proof. intros pc0 CTX regsT fp v H Hin. rewrite call_trace_cons. exact (H _ Hin). Qed.
Lemma llvmf_univ_call0 : forall (pc0 : Z) (CTX : list (list Z)) (regsT : bvmap 5 word),
(forall c, In c CTX ->
 In (firstn kUnwindMax (pc0 :: flat_map (fun r => if r =? pc0 then [] else [r]) c)) (as_universe B)) ->
In [raZ regsT] CTX ->
In (call_trace0 pc0 regsT []) (as_universe B).
Proof. intros pc0 CTX regsT H Hin. unfold call_trace0, unwind_of_chain. exact (H _ Hin). Qed.

(* ---- the segment statements ------------------------------------------------------------------------------ *)
(* Each is `start -> SRr SEGS W2 c2 end`. A lane proves one in its own file; this file does not move. *)

(* A 0x8070c..0x8098c, 160 slots. The prologue: the 320-byte frame, sp aligned to 32, the class-4 side-stack
   frame (stack_malloc_4 at 0x80780), the exclusion of the machine-stack fallback (0x8079c..0x807b4: the
   use-after-return flag is 1 by AR_const_law through PALibF's palf_got_uar, and the allocation returns a frame
   at or above 4096 by frames_bounds), the three frame-description words and the whole frame's shadow. *)
Definition seg_A : Prop :=
forall g W2 c2, inv_entry g W2 c2 -> e_pre g ->
SRr SEGS W2 c2 (fun W3 c3 => exists pos mf, inv_A_end g pos mf W3 c3).

(* B 0x8098c..0x80a7c, 60 slots. The eight start-up checks: reac_identity_init twice, reac_identity_ingest
   twice (both refused), reac_identity_fw_str, reac_identity_reac_ver_str, reac_box_catalogue_defect and
   reac_box_family_of, each on a NULL or empty argument; every abort branch is decided by the callee's post. *)
Definition seg_B : Prop :=
forall g pos mf W2 c2, inv_A_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_B_end g pos mf).

(* C 0x80a7c..0x80b20, 41 slots. __asan_memset of `hw`, the two guards (0x80a8c beqz s2 and 0x80ad4 beqz a2,
   both to 0x8157c) and the loop's head. With no record the run leaves the loop at once. *)
Definition seg_C : Prop :=
forall g pos mf W2 c2, inv_B_end g pos mf W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => inv_rec g pos mf 0 W3 c3 \/ (m_nrec g = 0%nat /\ inv_exit g pos mf W3 c3)).

(* D1 0x80b20..0x80d04, 121 slots. One record: the header read, fuzz_take, the payload copy (malloc + memcpy),
   reac_identity_ingest on it, the guard copy (malloc + memcpy + the 'Z' byte), reac_identity_ingest on the
   copy, the free of the guard copy, and the same_id compares up to 0x80d04. *)
Definition seg_D1 : Prop :=
forall g pos mf i W2 c2, inv_rec g pos mf i W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => exists pl, inv_D1_end g pos mf i pl W3 c3).

(* D2 0x80d04 to the four exits, 135 slots. The rest of the same_id and ignored-record checks and the switch on
   the record's address (measured): its exits are the three cases and the join. *)
Definition seg_D2 : Prop :=
forall g pos mf i pl W2 c2, inv_D1_end g pos mf i pl W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 =>
inv_caseV g pos mf i pl W3 c3 \/ inv_caseM g pos mf i pl W3 c3 \/
inv_caseF g pos mf i pl W3 c3 \/ inv_tail g pos mf i pl W3 c3).

(* D3 0x80f20..0x813b4, the REAC-version case: the three put_dec calls that build the expected string in `ev`,
   reac_identity_reac_ver_str into `v`, the bcmp of the two, the update of `hw`, and the jump to the join. *)
Definition seg_D3 : Prop :=
forall g pos mf i pl W2 c2, inv_caseV g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_tail g pos mf i pl).

(* D4 0x81170..0x813b4, the model-name case: memchr for the NUL in id.model_name, the bcmp of the name against
   the payload, and the stopped-early check. *)
Definition seg_D4 : Prop :=
forall g pos mf i pl W2 c2, inv_caseM g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_tail g pos mf i pl).

(* D5 0x81208..0x813b4, the firmware case: the four digit checks, reac_identity_fw_str into `s`, check_str and
   the five checks of the printed string. *)
Definition seg_D5 : Prop :=
forall g pos mf i pl W2 c2, inv_caseF g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_tail g pos mf i pl).

(* D6 0x813b4..0x81400, 19 slots. The record's tail: the cursor advance, the re-poisoning of `before` and
   `again` (0x813c4..0x813e8), the free of the payload copy and the loop test's operands. *)
Definition seg_D6 : Prop :=
forall g pos mf i pl W2 c2, inv_tail g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_D6_end g pos mf i).

(* The loop test 0x81400: on to the next record, or out to 0x8157c. *)
Definition seg_loop : Prop :=
forall g pos mf i W2 c2, inv_D6_end g pos mf i W2 c2 -> (S i < m_nrec g)%nat ->
SRr SEGS W2 c2 (inv_rec g pos mf (S i)).
Definition seg_rec_exit : Prop :=
forall g pos mf i W2 c2, inv_D6_end g pos mf i W2 c2 -> S i = m_nrec g ->
SRr SEGS W2 c2 (inv_exit g pos mf).

(* E 0x8157c..0x815f8, 31 slots (0x815f0 is skipped on the no-match path: 0x815d0 beqz s6,815f8).
   reac_box_family_of on the decoded identity, the inlined family_of_hw loop over HW_TABLE (bcmp at 0x815b8,
   three rows) and the check that the two agree. *)
Definition seg_E : Prop :=
forall g pos mf W2 c2, inv_exit g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_E_end g pos mf).

(* F 0x815f8..0x816e4, 59 slots. The ten tail bytes: the family byte, the two widths, the five capacities, the
   catalogue row and the 16-bit firmware value, each read from the input block and reduced. *)
Definition seg_F : Prop :=
forall g pos mf W2 c2, inv_E_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_F_end g pos mf).

(* G 0x816e4..0x817bc, 54 slots. The two capacity-chosen heap buffers: malloc, reac_identity_fw_str twice and
   check_str twice on the first, reac_identity_reac_ver_str and check_str on the second, and the two frees. *)
Definition seg_G : Prop :=
forall g pos mf W2 c2, inv_F_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_G_end g pos mf).

(* H 0x817bc..0x81878, 47 slots. The any-firmware block: two put_dec calls into `ef`, reac_identity_fw_str into
   `f` at the documented capacity, the bcmp that they agree, and the re-poisoning of f / ef. *)
Definition seg_H : Prop :=
forall g pos mf W2 c2, inv_G_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_H_end g pos mf).

(* I 0x81878..0x81974, 63 slots. The family (reac_box_family_of when t_fam_raw < 128, else t_fam_raw & 127),
   reac_box_family_stem, the three output buffers, and the two reac_box_name calls (the second with the input's
   widths), up to the 16-byte pop after the second (0x81970). *)
Definition seg_I : Prop :=
forall g pos mf W2 c2, inv_H_end g pos mf W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => exists nm tk dp, inv_I_end g pos mf nm tk dp W3 c3).

(* J 0x81974..0x81e60, 315 slots. The width check, the expected name and display: the stem copy loop, the widths
   through put_dec, the four copy loops of the display, the memchr of '-' and the fits check. With bad widths
   (n_wok = false, so r = -1) the run goes 0x81a2c -> 0x81e68 -> 0x82090 and ends at inv_K_end; the composition
   then goes straight to seg_L (measured on fuzz_identity.asan). *)
Definition seg_J : Prop :=
forall g pos mf nm tk dp W2 c2, inv_I_end g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => inv_J_end g pos mf nm tk dp W3 c3 \/
(SlotModel.n_wok (e_pl g) = false /\ inv_K_end g pos mf nm tk dp W3 c3)).

(* K 0x81e60..0x82090, 140 slots. The r = 0 checks: three strlen / check_str pairs, strcmp of the name and of
   the display, the token loop, reac_box_catalogue and the two reac_box_catalogue_defect calls. *)
Definition seg_K : Prop :=
forall g pos mf nm tk dp W2 c2, inv_J_end g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (inv_K_end g pos mf nm tk dp).

(* L 0x82090..0x82178, 58 slots. The three frees, the frame release (the flag word at SF+1016 and
   __asan_set_shadow_f5 over the frame's 128 shadow bytes), the epilogue and the return with a0 = 0. *)
Definition seg_L : Prop :=
forall g pos mf nm tk dp W2 c2, inv_K_end g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (inv_ret g (LL 0 (m_fs (e_md g)) [])).

(* ---- the composition ------------------------------------------------------------------------------------- *)
(* The walk is the segments chained from the entry to the return, under the contract's pre-condition; the
   continuation of the contract is applied at the return, where the leaf is LL 0 (m_fs md) [] (identity's
   library shape, HLIBK). The record loop is SRr_loop on nrec - i (inv_rec carries i < nrec); with bad widths
   seg_J ends at inv_K_end and the walk goes straight to seg_L. *)
Definition pb_LLVMFuzzerTestOneInput_stmt : Prop :=
seg_A -> seg_B -> seg_C -> seg_D1 -> seg_D2 -> seg_D3 -> seg_D4 -> seg_D5 -> seg_D6 ->
seg_loop -> seg_rec_exit -> seg_E -> seg_F -> seg_G -> seg_H -> seg_I -> seg_J -> seg_K -> seg_L ->
@tLLVMFuzzerTestOneInput_spec fx rc SK PI B MT XM_LIB XN_LIB RLO RHI LS RA_LLVMF A_EMPTY LLVMF_STK
EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.

(* The contract's library-shape hypothesis (LLVMFuzzerTestOneInput.v HLIBK). *)
Hypothesis HLIBK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).

(* The boundary P of a cut, without the cut's common part. *)
Lemma acut_P : forall g pos mf k pc P W2 c2, acut g pos mf k pc P W2 c2 ->
exists ly2 S2 regs2 mem2 md2, P ly2 S2 W2 regs2 mem2 md2.
Proof.
intros g pos mf k pc P W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & HP).
exists ly2, S2, regs2, mem2, md2. exact HP.
Qed.

Theorem pb_LLVMFuzzerTestOneInput : pb_LLVMFuzzerTestOneInput_stmt.
Proof.
intros hA hB hC hD1 hD2 hD3 hD4 hD5 hD6 hLP hRX hE hF hG hH hI hJ hK hL.
intros ly S0 W regs mem md p n pl M K HAI Hpre Hk.
rewrite HLIBK.
set (g := mkEctx ly S0 W mem md regs p n pl M).
assert (HW : SRr SEGS W (cfg_at SEGS A_LLVMFuzzerTestOneInputP regs mem md) (inv_ret g (LL 0 (m_fs md) []))).
{ eapply SRr_bind; [exact (hA g W _ (conj eq_refl eq_refl) Hpre)|].
  intros W1 c1 _ (pos & mf & H1).
  eapply SRr_bind; [exact (hB g pos mf W1 c1 H1)|]. intros W2 c2 _ H2.
  (* from the loop's exit to the return *)
  assert (EXIT : forall W3 c3, inv_exit g pos mf W3 c3 -> SRr SEGS W3 c3 (inv_ret g (LL 0 (m_fs md) []))).
  { intros W3 c3 H3.
    eapply SRr_bind; [exact (hE g pos mf W3 c3 H3)|]. intros W4 c4 _ H4.
    eapply SRr_bind; [exact (hF g pos mf W4 c4 H4)|]. intros W5 c5 _ H5.
    eapply SRr_bind; [exact (hG g pos mf W5 c5 H5)|]. intros W6 c6 _ H6.
    eapply SRr_bind; [exact (hH g pos mf W6 c6 H6)|]. intros W7 c7 _ H7.
    eapply SRr_bind; [exact (hI g pos mf W7 c7 H7)|]. intros W8 c8 _ (nm & tk & dp & H8).
    eapply SRr_bind; [exact (hJ g pos mf nm tk dp W8 c8 H8)|]. intros W9 c9 _ [H9 | [_ H9]].
    - eapply SRr_bind; [exact (hK g pos mf nm tk dp W9 c9 H9)|]. intros W10 c10 _ H10.
      exact (hL g pos mf nm tk dp W10 c10 H10).
    - exact (hL g pos mf nm tk dp W9 c9 H9). }
  (* the record loop, on nrec - i *)
  assert (LOOP : forall i W3 c3, inv_rec g pos mf i W3 c3 -> SRr SEGS W3 c3 (inv_exit g pos mf)).
  { apply (SRr_loop SEGS nat (fun i => (m_nrec g - i)%nat) (fun i => inv_rec g pos mf i) (inv_exit g pos mf)).
    intros i W3 c3 H3.
    eapply SRr_bind; [exact (hD1 g pos mf i W3 c3 H3)|]. intros W4 c4 _ (pl0 & H4).
    eapply SRr_bind; [exact (hD2 g pos mf i pl0 W4 c4 H4)|]. intros W5 c5 _ H5.
    eapply SRr_bind with (R := inv_tail g pos mf i pl0).
    { destruct H5 as [H5 | [H5 | [H5 | H5]]].
      - exact (hD3 g pos mf i pl0 W5 c5 H5).
      - exact (hD4 g pos mf i pl0 W5 c5 H5).
      - exact (hD5 g pos mf i pl0 W5 c5 H5).
      - apply SRr_ret. exact H5. }
    intros W6 c6 _ H6.
    eapply SRr_bind; [exact (hD6 g pos mf i pl0 W6 c6 H6)|]. intros W7 c7 _ H7.
    destruct (acut_P _ _ _ _ _ _ _ _ H7) as (ly7 & S7 & regs7 & mem7 & md7 & Hlt & _).
    destruct (Nat.lt_ge_cases (S i) (m_nrec g)) as [Hs | Hs].
    - eapply SRr_mono; [exact (hLP g pos mf i W7 c7 H7 Hs)|].
      intros W8 c8 _ H8. right. exists (S i). split; [clear - Hs; lia | exact H8].
    - eapply SRr_mono; [exact (hRX g pos mf i W7 c7 H7 ltac:(clear - Hlt Hs; lia))|].
      intros W8 c8 _ H8. left. exact H8. }
  eapply SRr_bind; [exact (hC g pos mf W2 c2 H2)|]. intros W3 c3 _ [H3 | [_ H3]].
  - eapply SRr_bind; [exact (LOOP 0%nat W3 c3 H3)|]. intros W4 c4 _ H4. exact (EXIT W4 c4 H4).
  - exact (EXIT W3 c3 H3). }
apply (SRr_srealizes SEGS W _ _ _ HW HAI).
intros W' c' Hle HAI' Hret. exact (Hk _ W' c' Hle HAI' Hret).
Qed.

End c.
End b.
End a.

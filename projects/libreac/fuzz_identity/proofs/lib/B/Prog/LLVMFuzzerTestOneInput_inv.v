(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput.v; 417 of its 466 lines of code are new or changed and 178 lines of the source are left out. *)
(* The boundary layer of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): one state predicate per phase
   boundary of the listing, the statement of each segment lemma, and the composition. The only proofs here are
   the one-line allocator-trace lemmas llvmf_univ_call / llvmf_univ_call0; the lanes prove
   `Lemma seg_X : seg_X_stmt` in their own files and the top proves the composition.

   Shape. A boundary is a `world SEGS -> config -> Prop`, as an SRr post-condition is: `acut g pos mf k pc P`
   says the run is at slot pc of the listing, the journal from the entry state g holds with the entry's one
   side-stack frame (4, pos) as its `own`, k events have been counted, and P holds of the state. A segment is
   `forall ..., <start> W2 c2 -> SRr SEGS W2 c2 (<end> ...)`.

   This is the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v:
   same names wherever the cut exists on both builds, with image B's slots, offsets and
   registers, measured on the neutral listing of fuzz_identity.asan-ubsan
   (the LLVMFuzzerTestOneInput listing).
   Addresses are given as the offset from the entry, i.e. the identb_listing slot, as `BASE + 0xNNN`.

   What a boundary carries: the slot, the journal and its event count, the frame (4, pos) and the machine frame
   mf, the registers the next segment reads, the bytes of the side-stack frame's live variables and of the
   machine frame's slots, the shadow of each live variable, the live heap blocks, and the value each holds in
   the plain model of the harness (lib/Prog/SlotModel.v, RcIdentModel.v), which is a function of
   the input bytes alone.

   A lane that finds its segment needs one more fact does not edit this file: it reports the fact to this
   file's owner, who adds it to the end of the segment before it and to the start of its own. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
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
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput.
(* The plain model of the harness: address-free, a function of the input bytes. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The side-stack frame's variables, from the frame description at object 2 (0x13d2c). Image B's frame
   description is image A's, so these offsets are A's. *)
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
(* The machine frame's two uninstrumented counter slots (put_dec's `n` argument): mf+208 for `ev`, `ef` and
   `w4` (0x81130, 0x81150, 0x81934, 0x81970), mf+200 for `exp_dp` (0x81c4c, 0x81f40, 0x81fe4). *)
Definition M_n1 : Z := 208.      Definition M_n2 : Z := 200.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
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
   the wrappers ask of a range they read. *)
Definition sh_blk (W2 : world SEGS) (mem2 : word -> option byte) (a n : Z) : Prop :=
block_shadow (aview SEGS (w_H W2) mem2) SHADOW_OFF a n.
Definition sh_zero (W2 : world SEGS) (mem2 : word -> option byte) (a n : Z) : Prop :=
zero_shadow (aview SEGS (w_H W2) mem2) SHADOW_OFF a n.

(* The contract's pre-condition at the entry state, as one name: a fact about g alone, never re-proved. A
   segment that needs the read-only image, the sink, the meta table, the fds / fs or the input block at its own
   state derives it from this and acut's journal (HRO with IdentBase.arodata_ok_journalP; ASINK_NONE_KEPT and
   AMETA_INV_KEPT; AJ_NIL_IO). *)
Definition e_pre (g : ectx) : Prop :=
tLLVMFuzzerTestOneInput_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS
(e_regs g) (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) (e_pl g) (e_M g).

(* What every boundary after the prologue carries. Image B's machine-frame slots (measured):
   0x807b4 (andi sp,sp,-32), 0x807b8 (mv s1,sp), 0x807b0 (addi s0,sp,320), 0x807dc (sd a7,168(s1), the shadow
   base), 0x809ec (sd s4,16(s1)), 0x809f0 (sd a6,64(s1)) and 0x80820 (sd a6,192(s1), the frame address), and
   the thirteen callee-saved words of the prologue 0x8077c..0x807ac, which the epilogue restores at
   0x8240c..0x8243c. The frame's shadow address lives at mf+160 until segment F overwrites that slot with
   `out_ch` (0x81868, 0x81c20), so it is in mf_fixed and in x23 (sh_reg), not here. *)
Definition ecommon (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
getr regs2 2 = w64 mf /\ getr regs2 9 = w64 mf /\ getr regs2 8 = w64 (e_sp0 g) /\
e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ mf mod 32 = 0 /\
getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
val_mem SEGS (rd W2 mem2) (mf + 16) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 64) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 192) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 SHADOW_OFF /\
(* the entry's own saved return address and frame pointer, for the call chain of every call it makes *)
val_mem SEGS (rd W2 mem2) (e_sp0 g - 8) 8 RA_LLVMF /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 16) 8 (s0Z (e_regs g)) /\
(* the eleven other callee-saved words of the prologue (s1 .. s11) *)
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
(* the frame's flag word, written by the prologue (0x80824..0x80854) and read by the release (0x823ec) *)
val_mem SEGS (rd W2 mem2) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos) /\
(* the contract's pre-condition of the entry state: it speaks of g alone, so it holds at every boundary *)
e_pre g /\
(forall fd, fd_lookup (m_fds md2) fd = fd_lookup (m_fds (e_md g)) fd) /\
m_fs md2 = m_fs (e_md g) /\
bytes_at8 W2 mem2 (e_p g) (e_pl g).

(* A boundary: at slot pc, with the journal from the entry state and the entry's own frame. The meter is
   carried event by event: what the run has spent, and what is left. *)
Definition MEV : Z := mo_malloc MT 256 + mo_free MT.
Definition acut (g : ectx) (pos mf k : Z) (pc : Z)
(P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = cfg_at SEGS pc regs2 mem2 md2 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k /\
frames S2 = [(4, pos)] /\ 0 <= k <= EV_LLVMF /\
mo_le MT (e_S g) S2 (k * MEV) /\
mo_ok MT S2 ((EV_LLVMF - k) * MEV) /\
ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 /\
P ly2 S2 W2 regs2 mem2 md2.

(* The heap blocks of the run, as a list; `hblocks` says exactly these are live beyond the entry's. *)
Definition hblocks (g : ectx) (ly2 : alayout) (S2 : astate) (hs : list (Z * Z)) : Prop :=
Permutation (ablocks B ly2 S2) (hs ++ ablocks B (e_ly g) (e_S g)) /\
Forall (fun h => 4096 <= fst h /\ 0 <= snd h) hs.

(* ---- the model of the harness, from the plain files ------------------------------------------------------ *)
Definition m_id (g : ectx) (i : nat) : list byte := SlotModel.rec_id (e_pl g) i.
Definition m_have (g : ectx) (i : nat) : Z := SlotModel.rec_have (e_pl g) i.
Definition m_hwb (g : ectx) (i : nat) : list byte := SlotModel.rec_hwb (e_pl g) i.
Definition m_cur (g : ectx) (i : nat) : Z := SlotModel.rec_c (e_pl g) i.
Definition m_nrec (g : ectx) : nat := SlotModel.nrecn (e_pl g).
(* `id` (38 bytes at SF+352): its bytes, and its shadow as seg_B sets it at 0x809f8..0x80a0c (four 0 cells and a
   last cell 6), never re-poisoned before L (0x823a8, 0x823b8..0x823c4): sh_zero is the four full cells, sh_blk
   the whole object, which the wrappers, reac_identity_ingest, reac_box_family_of and reac_box_name ask. *)
Definition id_at (g : ectx) (pos : Z) (i : nat) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
bytes_at8 W2 mem2 (SFa g pos + V_id) (m_id g i) /\ sh_zero W2 mem2 (SFa g pos + V_id) N_id /\
sh_blk W2 mem2 (SFa g pos + V_id) N_id.
(* The harness's `hw` block. B keeps its `have` word in the machine frame (mf+24) for the whole record loop and
   writes it into the frame variable only after the loop (0x8176c); the eight payload bytes are written in the
   frame by the version case (0x81288, 0x8128c). So the loop's form and the post-loop form differ. `hw`'s shadow
   is set at 0x80ad0 / 0x80ad4 (a 0 cell and a last cell 4) and never re-poisoned before L (0x823ac, 0x823b0);
   seg_E's bcmp at 0x817a4 reads SF+436..443. *)
Definition hw_mem (g : ectx) (pos : Z) (i : nat) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
bytes_at8 W2 mem2 (SFa g pos + V_hw + 4) (m_hwb g i) /\ sh_zero W2 mem2 (SFa g pos + V_hw) N_hw /\
sh_blk W2 mem2 (SFa g pos + V_hw) N_hw.
Definition hw_live (g : ectx) (pos mf : Z) (i : nat) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
hw_mem g pos i W2 mem2 /\
val_mem SEGS (rd W2 mem2) (SFa g pos + V_hw) 4 0 /\
val_mem SEGS (rd W2 mem2) (mf + 24) 8 (m_have g i).
Definition hw_at (g : ectx) (pos : Z) (i : nat) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
hw_mem g pos i W2 mem2 /\ val_mem SEGS (rd W2 mem2) (SFa g pos + V_hw) 4 (m_have g i).
(* The input cursor the record loop keeps in x25 (0x80b90, 0x815e0). The remaining length n - c is in x24
   (0x80b4c s8 = n - 1 with rec_c 0 = 1; 0x8159c s8 = mf+120 - s6 = rec_Lp i - rec_k i; 0x81758 s8 = 0 on the
   n = 0 path): inv_rec, inv_D6_end and inv_exit state it. *)
Definition cur_at (g : ectx) (i : nat) (regs2 : bvmap 5 word) : Prop :=
getr regs2 25 = w64 (e_p g + m_cur g i) /\ 0 <= m_cur g i <= e_n g.
(* The ten machine-frame slots that keep their value from the prologue to the end of the record loop
   (0x80af0..0x80bb0). mf+56 is the UBSan bound of the `ev` index, the bitwise complement of &ev. Only
   mf+160, mf+32 and mf+136 are stored before the two guards (0x80afc, 0x80b54): the boundaries the guard
   paths reach carry mf_hw and mf_id3 instead. *)
Definition mf_fixed (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 32) 8 (SFa g pos + V_hw) /\
val_mem SEGS (rd W2 mem2) (mf + 48) 8 (SFa g pos + V_v) /\
val_mem SEGS (rd W2 mem2) (mf + 56) 8 (Z.lnot (SFa g pos + V_ev)) /\
val_mem SEGS (rd W2 mem2) (mf + 72) 8 (SFa g pos + V_ev) /\
val_mem SEGS (rd W2 mem2) (mf + 80) 8 (SFa g pos + V_again + 28) /\
val_mem SEGS (rd W2 mem2) (mf + 88) 8 (SFa g pos + V_again + 3) /\
val_mem SEGS (rd W2 mem2) (mf + 104) 8 (SFa g pos + V_id + 28) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SFa g pos + V_id + 3) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SFa g pos + V_s) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (shadow_addr (SFa g pos)).
(* mf+32 holds &hw from 0x80af4 (read by seg_E at 0x81764); mf+136 holds &id+3 from 0x80af8 (read by seg_I at
   0x81a50 and seg_J at 0x81bb8, overwritten by seg_J at 0x81c38). Both are stored before the two guards, so
   they reach the loop exit on every path; mf_fixed holds both (its first and eighth conjuncts). *)
Definition mf_hw (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 32) 8 (SFa g pos + V_hw).
Definition mf_id3 (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SFa g pos + V_id + 3).
(* mf+152 holds &before from 0x80b64 until segment I stores the name buffer there (0x81a60). *)
Definition mf_before (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 152) 8 (SFa g pos + V_before).
(* mf+176 holds &again from 0x80b9c until segment F stores t_in there (0x8185c). *)
Definition mf_again (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SFa g pos + V_again).
(* mf+184 holds &id from 0x80a18 until 0x81a88, where segment I overwrites it with the display buffer. *)
Definition mf_id (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id).
(* The frame's shadow address in x23, from 0x815a0 / 0x817ec to the release at 0x823e4. *)
Definition sh_reg (g : ectx) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 23 = w64 (shadow_addr (SFa g pos)).
(* What the record loop carries from one record to the next. *)
Definition rec_live (g : ectx) (pos mf : Z) (i : nat) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 96) 8 (SlotModel.nrec (e_pl g)) /\
mf_fixed g pos mf W2 mem2 /\ mf_before g pos mf W2 mem2 /\ mf_again g pos mf W2 mem2 /\
mf_id g pos mf W2 mem2 /\ cur_at g i regs2 /\
id_at g pos i W2 mem2 /\ hw_live g pos mf i W2 mem2 /\ hblocks g ly2 S2 [].

(* ---- the boundaries ---------------------------------------------------------------------------------------- *)

(* 0x80774, the entry: the contract's pre-condition, before the frame exists. *)
Definition inv_entry (g : ectx) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = e_W g /\ c2 = cfg_at SEGS A_LLVMFuzzerTestOneInputP (e_regs g) (e_mem g) (e_md g).

(* +0x280 (0x809f4), A -> B: the class-4 frame is taken, its description words and the flag word are written,
   and every variable's shadow is poisoned; the machine frame holds the frame pointer (0x809ec sd s4,16(s1))
   and the frame address (0x809f0 sd a6,64(s1)), which ecommon states, and a6 still holds the frame address B
   reads at 0x809f4. (0x807e8 stack_malloc_4; 0x8084c..0x80854 the three description words; 0x80860..0x809e0
   the shadow.) The `size >= 2 ^ 26` exit at 0x809e4 is refuted by e_pre; x18 = n and x25 = p. *)
Definition inv_A_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf 0 (BASE + 0x280)
(fun ly2 S2 W2 regs2 mem2 md2 =>
val_mem SEGS (rd W2 mem2) (SFa g pos) 8 0x41b58ab3 /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 8) 8 (VAL (A_OBJ 2)) /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 16) 8 (VAL (A_OBJ 3)) /\
hblocks g ly2 S2 [] /\ sh_reg g pos regs2 /\ getr regs2 16 = w64 (SFa g pos) /\
getr regs2 18 = w64 (e_n g) /\ getr regs2 25 = w64 (e_p g)).

(* +0x370 (0x80ae4), B -> C: the slot of the __asan_memset call that clears `hw`. The eight start-up checks
   passed; `id` holds ID0 (SlotModel rec_id _ 0) and the pointer to it is in mf+184 (0x80a18). The memset's
   arguments are in place (0x80ac4..0x80ae0), `hw`'s two shadow bytes are set (0x80ad0 0, 0x80ad4 4), and the
   cursor registers still hold the input block. *)
Definition inv_B_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf 0 (BASE + 0x370)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos 0 W2 mem2 /\ hblocks g ly2 S2 [] /\ mf_id g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
getr regs2 19 = w64 (SFa g pos + V_hw) /\
getr regs2 10 = w64 (SFa g pos + V_hw) /\ getr regs2 11 = w64 0 /\ getr regs2 12 = w64 12 /\
getr regs2 18 = w64 (e_n g) /\ getr regs2 25 = w64 (e_p g) /\
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 /\
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4).

(* +0x440 (0x80bb4), the record loop's head after i records. The loop is rotated: 0x80bb4 is reached only with
   i < nrec (the guards 0x80afc and 0x80b54, both to the exit, and the test 0x815ec), so inv_rec carries
   i < nrec. The index is in x14 and x15 holds 1 (0x80b58, 0x80b8c, 0x815d8..0x815e8); x24 = n - c (0x80b4c,
   0x8159c) and x23 = the frame's shadow address (0x8085c, 0x815a0), through which D1 clears before's shadow
   (0x80cbc..0x80cd0). `before` and `again` are poisoned here (0xf8 from the prologue, 0x80874..0x808bc, and
   again from the re-poisoning 0x815a8..0x815cc); a segment that needs that states it from those stores. *)
Definition inv_rec (g : ectx) (pos mf : Z) (i : nat) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i) (BASE + 0x440)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\ getr regs2 14 = w64 (Z.of_nat i) /\ getr regs2 15 = w64 1 /\
getr regs2 24 = w64 (e_n g - m_cur g i) /\ sh_reg g pos regs2 /\
rec_live g pos mf i ly2 S2 W2 regs2 mem2).

(* +0xff0 (0x81764), the loop's exit: the two guards (0x80afc n = 0 -> 0x81750; 0x80b54 nrec = 0 -> 0x81760)
   and the loop test (0x815ec) all jump here. On the two guard paths only mf+160 (0x80af0), mf+32 (0x80af4),
   mf+136 (0x80af8), mf+24 (0x80b40 / 0x81754) and mf+184 (0x80a18) of the machine frame's pointer slots are
   stored, so this boundary carries those and nothing of mf_fixed / mf_before / mf_again. x24 = n - c on all
   three paths (0x81758 s8 = 0 with n = 0; 0x80b4c s8 = n - 1 with nrec = 0; 0x8159c). E reads mf+32 (0x81764),
   mf+24 (0x81768), mf+184 (0x81770) and mf+160 (0x817ec); I reads mf+136 (0x81a50). *)
Definition inv_exit (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g)) (BASE + 0xff0)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hw_live g pos mf (m_nrec g) W2 mem2 /\
hblocks g ly2 S2 [] /\ mf_hw g pos mf W2 mem2 /\ mf_id3 g pos mf W2 mem2 /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (shadow_addr (SFa g pos)) /\
mf_id g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
cur_at g (m_nrec g) regs2 /\ getr regs2 24 = w64 (e_n g - m_cur g (m_nrec g))).

(* ---- the record body ------------------------------------------------------------------------------------- *)
(* What the switch, the four cases and the join share. `pl` is the payload copy made at 0x80c90; the guard copy
   made by buf_of at 0x80d0c is freed at 0x80da0, before the first case boundary. The machine-frame slots the
   body writes: mf+112 the cursor after the record (0x80ca4), mf+120 the record's remaining length after the
   header, rec_Lp (0x80c84, on all four header paths; read at 0x81598), mf+128 the record index (0x80c88). *)
Definition P_body (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
(ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
(i < m_nrec g)%nat /\ hblocks g ly2 S2 [(pl, SlotModel.rec_k (e_pl g) i)] /\
bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) /\
id_at g pos (S i) W2 mem2 /\
val_mem SEGS (rd W2 mem2) (mf + 96) 8 (SlotModel.nrec (e_pl g)) /\
mf_fixed g pos mf W2 mem2 /\ mf_before g pos mf W2 mem2 /\ mf_again g pos mf W2 mem2 /\
mf_id g pos mf W2 mem2 /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (e_p g + m_cur g (S i)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.rec_Lp (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (Z.of_nat i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 27 = w64 pl /\
0 <= m_cur g (S i) <= e_n g.

(* +0x630 (0x80da4), D1 -> D2: both copies are made, both ingest calls have run, the guard copy is freed, and
   the first result compare is next (0x80da4 beq s10,s4). x20 is the first ingest's result, x26 the second's,
   x18 the record's address. *)
Definition inv_D1_end (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0x630)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_live g pos mf i W2 mem2 /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
sh_blk W2 mem2 (SFa g pos + V_again) N_again /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
bytes_at8 W2 mem2 (SFa g pos + V_again) (m_id g (S i)) /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 20 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 26 = w64 (SlotModel.rec_r (e_pl g) i)).

(* The four exits of the switch (0x80e84 beqz x20 and 0x80e88 / 0x80e94 / 0x80ea0): the firmware case at
   0x80ea4, the ignored-record path at 0x80f28, the REAC-version case at 0x80ffc and the model-name case at
   0x812b8. Each carries the `again` fields its case reads, loaded by seg_D2 from again = m_id (S i): caseF
   byte 2 in x23 (0x80dc8, read 0x80eb0) and fw_milli in x26 (0x80db0, read 0x8140c); caseV has_reac_version
   in x10 (0x80e70), major in x24 (0x80e10), minor in x25 (0x80e28), patch in x21 (0x80e40); caseM
   has_model_name in x19 (0x80df8, read 0x812c8); the ignored path the record's address in x18. In the case
   bodies x23 is not the shadow address (caseV reloads mf+168 itself at 0x81020). *)
Definition inv_caseF (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0x730)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_live g pos mf i W2 mem2 /\
SlotModel.rec_r (e_pl g) i = 1 /\ SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_FIRMWARE /\
getr regs2 15 = w64 SHADOW_OFF /\
getr regs2 23 = w64 (RcIdentModel.bz (RcIdentModel.nthb (m_id g (S i)) 2)) /\
getr regs2 26 = w64 (RcIdentModel.fw_milli (m_id g (S i)))).
Definition inv_ignored (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0x7b4)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_live g pos mf i W2 mem2 /\
SlotModel.rec_r (e_pl g) i = 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i)).
Definition inv_caseV (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0x888)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_live g pos mf i W2 mem2 /\
SlotModel.rec_r (e_pl g) i = 1 /\ SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_REAC_VERSION /\
getr regs2 10 = w64 (RcIdentModel.has_reac_version (m_id g (S i))) /\
getr regs2 24 = w64 (RcIdentModel.major (m_id g (S i))) /\
getr regs2 25 = w64 (RcIdentModel.minor (m_id g (S i))) /\
getr regs2 21 = w64 (RcIdentModel.patch (m_id g (S i)))).
Definition inv_caseM (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0xb44)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_live g pos mf i W2 mem2 /\
SlotModel.rec_r (e_pl g) i = 1 /\ SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_MODEL_NAME /\
getr regs2 19 = w64 (RcIdentModel.has_model_name (m_id g (S i)))).

(* +0xe24 (0x81598), the join every case reaches: the record's tail, before the re-poisoning and the free.
   It reads mf+120 (0x81598), mf+160 into x23 (0x815a0) and the payload copy in x27 (0x815d0). *)
Definition inv_tail (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 3) (BASE + 0xe24)
(fun ly2 S2 W2 regs2 mem2 md2 =>
P_body g pos mf i pl ly2 S2 W2 regs2 mem2 /\ hw_live g pos mf (S i) W2 mem2).

(* +0xe78 (0x815ec), the loop test: the payload copy is freed, `before` and `again` are poisoned again
   (0x815a8..0x815cc), the cursor and the index are reloaded (0x815d8..0x815e8), so x14 = i + 1, x10 = nrec
   and x15 = 1; x24 = mf+120 - rec_k = n - c (0x8159c). *)
Definition inv_D6_end (g : ectx) (pos mf : Z) (i : nat) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat i + 4) (BASE + 0xe78)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\ getr regs2 14 = w64 (Z.of_nat (S i)) /\
getr regs2 10 = w64 (SlotModel.nrec (e_pl g)) /\ getr regs2 15 = w64 1 /\
getr regs2 24 = w64 (e_n g - m_cur g (S i)) /\ sh_reg g pos regs2 /\
rec_live g pos mf (S i) ly2 S2 W2 regs2 mem2).

(* +0x1080 (0x817f4), E -> F: `hw.have` is written into the frame variable (0x8176c), reac_box_family_of
   agrees with the harness's own table (the inlined family_of_hw loop at 0x81798..0x817b4), and the cursor is
   at the tail: x25 = p + c and x24 = n - c (both from the exit), x14 = the shadow offset (0x817bc / 0x817c8 /
   0x817d8, read 0x81808). E stores nothing in the machine frame; after E nothing reads mf+32 again. *)
Definition inv_E_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g)) (BASE + 0x1080)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hw_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
SlotModel.FAM (SlotModel.idT (e_pl g)) =
SlotModel.fam_hw (m_have g (m_nrec g)) (m_hwb g (m_nrec g)) /\
getr regs2 25 = w64 (e_p g + SlotModel.cT (e_pl g)) /\
getr regs2 24 = w64 (e_n g - SlotModel.cT (e_pl g)) /\
getr regs2 14 = w64 SHADOW_OFF).

(* +0x1128 (0x8189c), F -> G: the ten tail bytes are in registers and in four machine-frame slots (the in-line
   reads 0x817f8..0x8188c and the out-of-line block 0x82448..0x8260c). The boundary is the slot of the first
   buf_of call, whose argument is t_cap_fw (B calls buf_of, which takes the max itself; A, which inlines it,
   carries Z.max cap_fw 1 here). mf+184 still holds &id and mf+136 &id+3; mf+176 now holds t_in, mf+160 t_out,
   mf+112 the row and mf+120 the display capacity; x25 = &ef (0x8188c). *)
Definition inv_F_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g)) (BASE + 0x1128)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hw_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
getr regs2 25 = w64 (SFa g pos + V_ef) /\
getr regs2 10 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
getr regs2 22 = w64 (SlotModel.t_cap_ver (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 21 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
getr regs2 24 = w64 (SlotModel.t_any_fw (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g))).

(* +0x11c4 (0x81938), G -> H: the two capacity-chosen heap buffers were made, used by the formatters and
   freed; `f`'s shadow cell and `ef`'s two are cleared (0x81928..0x81930) and its counter slot is zero
   (0x81934). H reads x24, x25 (&ef, put_dec's a0 at 0x81958 / 0x819a8, bcmp's a1 at 0x819f4) and mf+208; x21,
   x26, x27 and the four tail slots pass through to I, J and K. *)
Definition inv_G_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x11c4)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\ sh_reg g pos regs2 /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
sh_zero W2 mem2 (SFa g pos + V_f) N_f /\ sh_zero W2 mem2 (SFa g pos + V_ef) N_ef /\
val_mem SEGS (rd W2 mem2) (mf + M_n1) 8 0 /\
getr regs2 24 = w64 (SlotModel.t_any_fw (e_pl g)) /\
getr regs2 25 = w64 (SFa g pos + V_ef) /\
getr regs2 21 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g))).

(* +0x128c (0x81a00), H -> I: the any-firmware block is done: `ef` holds the expected string and the
   formatter's output in `f` equals it (the bcmp at 0x819f8). This slot is before the family branch (0x81a14
   bltz a1). x22 = the display capacity (0x819e0 ld s6,120(s1)). I reads x27 (0x81a04), mf+184 (0x81a18,
   0x81a38), mf+136 (0x81a50), x21, x26 and x22 (0x81a40..0x81a70), mf+176 / mf+160 (0x81ad4, 0x81ad8). *)
Definition inv_H_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x128c)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ hblocks g ly2 S2 [] /\ sh_reg g pos regs2 /\
mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
bytes_at8 W2 mem2 (SFa g pos + V_ef) (SlotModel.t_EF (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
getr regs2 21 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g))).

(* +0x1388 (0x81afc), I -> J: the family and its stem are taken, the three output buffers are made, and the
   two reac_box_name calls have run (the refusing one at 0x81aac, the real one at 0x81aec). The boundary is
   past the 16-byte pop of the stack arguments (0x81af4), so sp = mf again; the result is in x24 (0x81af8) and
   still in a0 (0x81afc adds 1 to it), and a2 = the shadow offset (0x81af0). B keeps the three buffers in
   mf+152 (nm), x21 (tk) and mf+184 (dp); A keeps nm in mf+184. x18 = the family (0x81a20 / 0x81a28), x27 =
   id's has_model_name byte (0x81a3c), x22 = the display capacity; mf+144 = cap_name (0x81a58), mf+128 =
   cap_tok (0x81aa4). J reads mf+136 (0x81bb8). *)
Definition inv_I_end (g : ectx) (pos mf : Z) (nm tk dp : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1388)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ sh_reg g pos regs2 /\ mf_id3 g pos mf W2 mem2 /\
hblocks g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
getr regs2 24 = w64 (SlotModel.n_r (e_pl g)) /\ getr regs2 21 = w64 tk /\
getr regs2 10 = w64 (SlotModel.n_r (e_pl g)) /\ getr regs2 12 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SlotModel.t_cap_tok (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)) /\
(SlotModel.n_r (e_pl g) = 0 ->
bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0]))).

(* +0x1988 (0x820fc), J -> K: the expected name and display are built in the frame (the five copy loops and
   the four put_dec calls) and the width case is decided; the branch on r is next. Both paths in (0x81bb0 with
   bad widths, n_r = -1; 0x820f8) have set x25 = &exp_nm, x26 = &exp_dp (0x81b70, 0x81b74), cleared their shadow
   (0x81b78..0x81ba4) and stored the empty string in both (0x81ba8, 0x81bac). x22 = the display capacity
   (0x819e0, 0x820bc, 0x820dc). K reads x21, x22, x24, x25, x26, mf+112 / 128 / 144 / 152 / 160 / 176 / 184. *)
Definition inv_J_end (g : ectx) (pos mf : Z) (nm tk dp : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1988)
(fun ly2 S2 W2 regs2 mem2 md2 =>
hblocks g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
sh_reg g pos regs2 /\ getr regs2 24 = w64 (SlotModel.n_r (e_pl g)) /\
getr regs2 21 = w64 tk /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SlotModel.t_cap_tok (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
(SlotModel.n_wok (e_pl g) = true ->
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])) /\
(SlotModel.n_r (e_pl g) = 0 ->
bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0]))).

(* +0x1bec (0x82360), K -> L: every check of the r = 0 branch passed (the three strlen / check_str pairs, the
   two strcmp of name and display, the token loop, reac_box_catalogue and the two reac_box_catalogue_defect
   calls). The r <> 0 side reaches the same slot from 0x820fc. *)
Definition inv_K_end (g : ectx) (pos mf : Z) (nm tk dp : Z) : world SEGS -> config -> Prop :=
acut g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1bec)
(fun ly2 S2 W2 regs2 mem2 md2 =>
hblocks g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
sh_reg g pos regs2 /\ getr regs2 21 = w64 tk /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp).

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
   sp0, no record: `llvmf_univ_call _ _ _ _ _ HUMM` with `In [raZ regsT; RA_LLVMF] LLVMF_MALLOC_CTX`, or
   `llvmf_univ_call0 _ _ _ HUMM` with `In [raZ regsT] LLVMF_MALLOC_CTX` (HUMF and LLVMF_FREE_CTX for free).
   buf_of's contract asks `In (raZ regs :: spine ch) CTX_BUF_OF` directly. *)
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
(* Each is `start -> SRr SEGS W2 c2 end`. A lane proves `Lemma seg_X : seg_X_stmt` in its own file; this file
   does not move. The ranges are the listing offsets. *)

(* A +0x000..+0x280, 160 slots. The prologue: the 320-byte frame, sp aligned to 32, the class-4 side-stack
   frame (stack_malloc_4 at 0x807e8), the exclusion of the machine-stack fallback (0x80804..0x8081c: the
   use-after-return flag is 1 by AR_const_law through PALibF's palf_got_uar, and the allocation returns a frame
   at or above 4096 by frames_bounds), the three frame-description words, the flag word and the whole frame's
   shadow, and the two machine-frame stores 0x809ec / 0x809f0. The `size >= 2 ^ 26` exit (0x809e4) is refuted
   by e_pre; seg_early states it separately. *)
Definition seg_A_stmt : Prop :=
forall g W2 c2, inv_entry g W2 c2 -> e_pre g ->
SRr SEGS W2 c2 (fun W3 c3 => exists pos mf, inv_A_end g pos mf W3 c3).

(* B +0x280..+0x370, 60 slots. The eight start-up checks: reac_identity_init twice, reac_identity_ingest twice
   (both refused), reac_identity_fw_str, reac_identity_reac_ver_str, reac_box_catalogue_defect and
   reac_box_family_of, each on a NULL or empty argument; every abort branch is decided by the callee's post. *)
Definition seg_B_stmt : Prop :=
forall g pos mf W2 c2, inv_A_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_B_end g pos mf).

(* C +0x370..+0x440, 52 slots. __asan_memset of `hw` (12 bytes at SF+432), nrec = input[0] mod 65 through
   object 5's reciprocal, the hoisted machine-frame slots, the two guards (0x80afc beqz s2 and 0x80b54 beqz a1,
   both to the exit) and the loop's head. With no record the run leaves the loop at once. *)
Definition seg_C_stmt : Prop :=
forall g pos mf W2 c2, inv_B_end g pos mf W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => inv_rec g pos mf 0 W3 c3 \/ (m_nrec g = 0%nat /\ inv_exit g pos mf W3 c3)).

(* D1 +0x440..+0x630, 124 slots. One record: the header read, fuzz_take, the payload copy (malloc at 0x80c90 +
   memcpy), reac_identity_ingest on it, the guard copy (buf_of at 0x80d0c + memcpy + the 'Z' byte),
   reac_identity_ingest on the copy, and the free of the guard copy. *)
Definition seg_D1_stmt : Prop :=
forall g pos mf i W2 c2, inv_rec g pos mf i W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => exists pl, inv_D1_end g pos mf i pl W3 c3).

(* D2 +0x630 to the four exits, 65 slots. The same_id compares (bcmp at 0x80de8 and 0x80e60 and the field
   tests) and the switch on the record's address (0x80e84..0x80ea0). *)
Definition seg_D2_stmt : Prop :=
forall g pos mf i pl W2 c2, inv_D1_end g pos mf i pl W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 =>
inv_caseV g pos mf i pl W3 c3 \/ inv_caseM g pos mf i pl W3 c3 \/
inv_caseF g pos mf i pl W3 c3 \/ inv_ignored g pos mf i pl W3 c3).

(* D3r +0x7b4..+0xe24, the ignored-record path: the bcmp at 0x80f34 (`before` against `id`, 38 bytes) and the
   three checks that an accepted record would have been seen (0x80f44..0x81594). *)
Definition seg_D3r_stmt : Prop :=
forall g pos mf i pl W2 c2, inv_ignored g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_tail g pos mf i pl).

(* D3 +0x888..+0xe24, the REAC-version case: the field checks, the bcmp at 0x8101c, the three put_dec calls
   that build the expected string in `ev`, reac_identity_reac_ver_str into `v`, the bcmp of the two, and the
   update of `hw` (0x81284..0x812b0). *)
Definition seg_D3_stmt : Prop :=
forall g pos mf i pl W2 c2, inv_caseV g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_tail g pos mf i pl).

(* D4 +0xb44..+0xe24, the model-name case: memchr for the NUL in id.model_name (0x812c4), the bcmp of the name
   against the payload (0x81310) and the stopped-early check. *)
Definition seg_D4_stmt : Prop :=
forall g pos mf i pl W2 c2, inv_caseM g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_tail g pos mf i pl).

(* D5 +0x730..+0xe24, the firmware case: the four digit checks, reac_identity_fw_str into `s` (0x8142c),
   check_str (0x8143c) and the five checks of the printed string. *)
Definition seg_D5_stmt : Prop :=
forall g pos mf i pl W2 c2, inv_caseF g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_tail g pos mf i pl).

(* D6 +0xe24..+0xe78, 21 slots. The record's tail: the re-poisoning of `before` and `again`, the free of the
   payload copy (0x815d4) and the loop test's operands. *)
Definition seg_D6_stmt : Prop :=
forall g pos mf i pl W2 c2, inv_tail g pos mf i pl W2 c2 -> SRr SEGS W2 c2 (inv_D6_end g pos mf i).

(* The loop test 0x815ec: on to the next record (the back edge 0x815f0), or out to 0x81764. *)
Definition seg_loop_stmt : Prop :=
forall g pos mf i W2 c2, inv_D6_end g pos mf i W2 c2 -> (S i < m_nrec g)%nat ->
SRr SEGS W2 c2 (inv_rec g pos mf (S i)).
Definition seg_rec_exit_stmt : Prop :=
forall g pos mf i W2 c2, inv_D6_end g pos mf i W2 c2 -> S i = m_nrec g ->
SRr SEGS W2 c2 (inv_exit g pos mf).

(* E +0xff0..+0x1080, 36 slots. `hw.have` written into the frame (0x8176c), reac_box_family_of on the decoded
   identity (0x81774), the inlined family_of_hw loop over HW_TABLE (bcmp at 0x817a4, three rows) and the check
   that the two agree (0x817f0). *)
Definition seg_E_stmt : Prop :=
forall g pos mf W2 c2, inv_exit g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_E_end g pos mf).

(* F +0x1080..+0x1128, 42 slots in line plus the out-of-line block +0x1cd4..+0x1e98. The ten tail bytes: the
   family byte, the two widths, the five capacities, the catalogue row and the 16-bit firmware value, each read
   from the input block and reduced. *)
Definition seg_F_stmt : Prop :=
forall g pos mf W2 c2, inv_E_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_F_end g pos mf).

(* G +0x1128..+0x11c4, 39 slots. The two capacity-chosen heap buffers: buf_of, reac_identity_fw_str twice and
   check_str twice on the first, reac_identity_reac_ver_str and check_str on the second, the two frees, and the
   unpoisoning of `f` / `ef` and the counter slot (0x81928..0x81934). *)
Definition seg_G_stmt : Prop :=
forall g pos mf W2 c2, inv_F_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_G_end g pos mf).

(* H +0x11c4..+0x128c, 50 slots. The any-firmware block: two put_dec calls into `ef`, reac_identity_fw_str
   into `f` at the documented capacity, and the bcmp that they agree. *)
Definition seg_H_stmt : Prop :=
forall g pos mf W2 c2, inv_G_end g pos mf W2 c2 -> SRr SEGS W2 c2 (inv_H_end g pos mf).

(* I +0x128c..+0x1388, 63 slots. reac_box_family_of (when the input does not name the family),
   reac_box_family_stem, the three output buffers, and the two reac_box_name calls with their two stack
   arguments. *)
Definition seg_I_stmt : Prop :=
forall g pos mf W2 c2, inv_H_end g pos mf W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => exists nm tk dp, inv_I_end g pos mf nm tk dp W3 c3).

(* J +0x1388..+0x1988, 384 slots. The width decision and the expected name and display: the stem copy loop,
   the widths through put_dec, the four copy loops of the display, the memchr of '-' and the fits check. With
   bad widths (n_r = -1) the run goes 0x81bb0 -> 0x820fc, which is on both paths on B, so seg_J has one end
   (A's seg_J has two, its bad-width path skips its J -> K slot). *)
Definition seg_J_stmt : Prop :=
forall g pos mf nm tk dp W2 c2, inv_I_end g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (inv_J_end g pos mf nm tk dp).

(* K +0x1988..+0x1bec, 153 slots. The r = 0 checks: three strlen / check_str pairs, strcmp of the name and of
   the display, the token loop, reac_box_catalogue and the two reac_box_catalogue_defect calls. The r <> 0
   side is the branch at 0x820fc straight to +0x1bec. *)
Definition seg_K_stmt : Prop :=
forall g pos mf nm tk dp W2 c2, inv_J_end g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (inv_K_end g pos mf nm tk dp).

(* L +0x1bec..+0x1cd0, 57 slots. The three frees, the scope shadow stores, the frame release (the header word
   at 0x823d8, __asan_set_shadow_f5 over the frame's 128 shadow bytes at 0x823e8 and the flag byte at
   0x823f0), the epilogue and the return with a0 = 0. This segment also owns the early-return path of
   segment A, which enters at +0x1c5c (0x823d0) with k = 0 and no heap block. *)
Definition seg_L_stmt : Prop :=
forall g pos mf nm tk dp W2 c2, inv_K_end g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (inv_ret g (LL 0 (m_fs (e_md g)) [])).
Definition seg_early_stmt : Prop :=
forall g W2 c2, inv_entry g W2 c2 -> e_pre g -> 2 ^ 26 <= e_n g ->
SRr SEGS W2 c2 (inv_ret g (LL 0 (m_fs (e_md g)) [])).

(* ---- the composition ------------------------------------------------------------------------------------- *)
(* The walk is the segments chained from the entry to the return, under the contract's pre-condition; the
   continuation of the contract is applied at the return, where the leaf is LL 0 (m_fs md) [] (identity's
   library shape, HLIBK). *)
Definition pb_LLVMFuzzerTestOneInput_stmt : Prop :=
seg_A_stmt -> seg_B_stmt -> seg_C_stmt -> seg_D1_stmt -> seg_D2_stmt -> seg_D3r_stmt -> seg_D3_stmt ->
seg_D4_stmt -> seg_D5_stmt -> seg_D6_stmt -> seg_loop_stmt -> seg_rec_exit_stmt -> seg_E_stmt -> seg_F_stmt ->
seg_G_stmt -> seg_H_stmt -> seg_I_stmt -> seg_J_stmt -> seg_K_stmt -> seg_L_stmt -> seg_early_stmt ->
@tLLVMFuzzerTestOneInput_spec fx rc SK PI B MT XM_LIB XN_LIB RLO RHI LS RA_LLVMF A_EMPTY LLVMF_STK
EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.

End c.
End b.
End a.

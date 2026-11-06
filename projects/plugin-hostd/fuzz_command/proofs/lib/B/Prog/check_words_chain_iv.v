(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   entry to the memchr call 0x86ef8 (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/A/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ef8; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s1.v, with its module paths and module names changed; 322 of its 354 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/check_words_chain_iv.v for fuzz_command.asan-ubsan:
   module paths, the B image's runtime cells (0xa6bf8, 0x604158, 0xae455), its 224-byte frame, its spill slots and
   the registers its code keeps at the stage boundaries; the B statement's premises 0 <= wp < 2 ^ 64, cp mod 8 = 0
   and wp mod 8 = 0 (the UBSan checks of the tail and the loop) are in cwc_pre; cr_lit_tail takes a state of the
   record (CmdRecFacts' cmd_tail_vis_at gives it). Re-fitted to statement passes 4, 4b and 5: cwc_post
   is apost_baseF, the loop and the tail stages take rounding mode 0 (PaFx.v's frm0) and
   state their post at their own FP state. CwcRec's field cr_snp_rom of that touch is gone with the kit's
   cmd_snp_rom (the snprintf contract takes the caller's rt_rom_view and reads no list). *)
(* The interfaces between the stages of the walk of check_words_chain on the ASan+UBSan build of
   plugin-hostd/fuzz_command (fuzz_command.asan-ubsan, entry 0x890e0).

   The walk is cut where the code joins: the side-stack take at 0x89158 (check_words_chain_s1.v), the loop head
   0x892b4, the tail 0x89334 (the count text and the three checks of the recorded call) and the teardown 0x89408
   (the release of the side-stack frame and the epilogue). Each stage after the take is a lemma over concrete
   registers and memory, in the shape of cgif_file_fuzzer's own stage statements (lib/A/ACh6.v cl_midX,
   lib/A/AC8b.v tcbb_loopX): the stage builds its symbolic state again from the facts below, so a stage depends
   on the one before it only through these definitions.

   CwcRec names the facts about this binary's allocator record and image that the walk needs and that
   tcheck_words_chain_spec does not give (this port's decision of 2026-10-28 21:50Z: the statements take the
   per-binary record, and CmdRecFacts.v discharges these from it). Each field says what it is for. The
   final theorem does not take CwcRec: check_words_chain.v builds it inside its proof, field by field, from the
   walk hypotheses (HB, TL, TLF, IMG) and lib/B/Prog/CmdRecFacts.v.

   The FP state: each stage statement is a Definition of the section below, so it is stated at the section's FP
   state fx and, once the section is closed, holds at any. The loop and the tail call the snprintf wrapper, which
   returns at another FP state fx1 with PaFx.v's fxrel fx fx1; what follows the call (the loop's next turn, the
   tail's strcmp calls, the teardown) is the stage statement at fx1, whose post apost_baseF at fx1 is the post at
   fx again by PaFx.v's srr_apost_baseF_lift. So the loop and the tail take rounding mode 0 at their own FP state
   (frm0, which fxrel_frm0 carries to fx1), and the teardown, which calls no snprintf, does not.

   cwc_pre is the statement's premises at the entry; cwc_post its conclusion. cwc_mid is what holds at every
   stage boundary after the take: the journal from the entry with the class-4 frame (4, fpos) owned, the
   abstract state's blocks unchanged, the realigned stack pointer, the thirteen saved registers, the spill slots
   at sp1, the frame's flag word and the frame's shadow bytes that make list and count usable. cwc_rd and
   cwc_strk are a read range and a C string as the wrapper contracts take them, apart from the call's own stack
   window (which lies above alloc_ceiling); cwc_wordk is slot j of the harness's word array with its shadow
   byte. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c HarnessPropsA CwcText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_chain_c check_words_chain_s0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the thirteen registers the prologue saves, in the order of their slots below the entry sp: ra at sp0 - 8, s0 at
   sp0 - 16, s1 .. s11 below *)
Definition cwc_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* the text of the members 2 .. k-1 that list holds at the head of the loop for word k *)
Definition cwc_T (ws : list (list byte)) (k : Z) : list Z := chain_items_at atoi_a 2 (Z.to_nat (k - 2)) ws.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variables RLO RHI : Z.

(* a C string the statement hands over in a live block (lib/B/Prog/check_words_chain_c.v: the recorded arguments,
   blocks by acall_at, and the harness words in words_of's `copy` block): its address, the block that holds it
   with its terminator, and its bytes *)
Definition cwc_sblk ly S (rd : reader) (p : Z) (x : list byte) : Prop :=
0 <= p < 2 ^ 64 /\ in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\ astr_atR rd p x.

Record CwcRec : Prop := mkCwcRec {
(* the shadow cell, the GOT words and the errno cell of the record are the image's (cgif's PALib) *)
cr_tl : PALib B;
(* the use-after-return flag cell and the class entries of __asan_stack_malloc_N (cgif's PALibF) *)
cr_tlf : PALibF B;
(* every byte of the recorded calls of g_rec is marked usable (checks 2, 3, 4 of the tail) *)
cr_grec_ra : forall ly S W mem md, AR SEGS B ly S W mem md ->
  range_addressable (rdW W mem) SHADOW_OFF (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS);
(* g_rec lies in the image, apart from the runtime's own cells and the errno cell, so the journal keeps it *)
cr_grec_not_rt : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
(* the two format literals are marked usable through their NUL and their shadow words are readable *)
cr_lit_ra : forall ly S W mem md, AR SEGS B ly S W mem md ->
  range_addressable (rdW W mem) SHADOW_OFF A_FMT_D (LEN_FMT_D + 1) /\
  shadow_hull_vis (rdW W mem) A_FMT_D (LEN_FMT_D + 1) /\
  range_addressable (rdW W mem) SHADOW_OFF A_FMT_SPD (LEN_FMT_SPD + 1) /\
  shadow_hull_vis (rdW W mem) A_FMT_SPD (LEN_FMT_SPD + 1);
(* the bytes of the two format literals are image bytes that are not the runtime's own and not the errno cell,
   so the journal keeps them *)
cr_lit_ro : forall a, A_FMT_D <= a < A_FMT_D + LEN_FMT_D + 1 \/ A_FMT_SPD <= a < A_FMT_SPD + LEN_FMT_SPD + 1 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
(* musl's word-at-a-time loops read to the end of the literal terminator's 8-byte granule, at every state of the
   record (CmdRecFacts' cmd_tail_vis_at: both literals' ends are among CmdRo's cmd_ro_ends) *)
cr_lit_tail : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  atail_vis SEGS W mem (A_FMT_D + LEN_FMT_D) /\ atail_vis SEGS W mem (A_FMT_SPD + LEN_FMT_SPD);
(* a string in a live block: musl's word-at-a-time loops read to the end of its terminator's 8-byte granule
   (CmdRecFacts' cmd_heap_tail_vis, statement pass 3; the old check_words walk's "BLOCK_TAIL" gap) *)
cr_heap_tail : forall ly S W mem md p x, AR SEGS B ly S W mem md ->
  cwc_sblk ly S (rdW W mem) p x -> atail_vis SEGS W mem (p + astr_len x);
(* the second range of the read-only bytes lies in the image (PAImg's pa_relro_img, for RLO, RHI the image's
   relocated read-only range) *)
cr_relro_img : forall a, RLO <= a < RHI -> in_img SEGS a;
(* the cells the atoi and snprintf entries read, in every state of the record: the stack-protector GOT word and
   guard (aguard_ok), the replace_str flag byte, the errno cell. The statement takes them at the entry and says
   they are the record's (lib/B/Prog/check_words_chain_c.v:97-108); the walk calls those entries up to 63 times
   each, and the errno cell, the guard and the flag are image cells the side-stack take may count as the runtime's
   own, so the walk takes them at every call from the record. *)
cr_rt_cells : forall ly S W mem md, AR SEGS B ly S W mem md ->
  aguard_ok SEGS W mem 0xa6bf8 0x604158 /\ rdW W mem 0xae455 = Some 1 /\ (exists ev, rd32 (rdW W mem) (as_errno B) ev)
}.

(* the premises of tcheck_words_chain_spec (lib/B/Prog/check_words_chain_c.v:114-160), as one proposition; the
   statement's astack_pres is not used by the walk *)
Definition cwc_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (cp wp r nargs p1 p2 : Z) (pw : list Z)
  (ws : list (list byte)) (x1 x2 : list byte) : Prop :=
afn_pre SEGS B CHECK_WORDS_CHAIN_STK ly S W regs mem md ch /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
getr regs 10 = w64 cp /\ getr regs 11 = w64 wp /\ getr regs 12 = w64 r /\
0 <= r <= 64 /\ 0 <= wp < 2 ^ 64 /\
cmd_ro_ok (rdW W mem) /\
cmd_val_objs /\
aguard_ok SEGS W mem 0xa6bf8 0x604158 /\
rdW W mem 0xae455 = Some 1 /\
(exists ev, rd32 (rdW W mem) (as_errno B) ev) /\
A_G_REC + OFF_CALLS <= cp /\ cp + CALL_SIZE <= A_G_REC + REC_SIZE /\ cp mod 8 = 0 /\
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 nargs /\ 0 <= nargs <= 6 /\
(nargs = 3 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 8) 8 p1 /\
 cwc_sblk ly S (rdW W mem) p1 x1) /\
(nargs = 3 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 16) 8 p2 /\
 cwc_sblk ly S (rdW W mem) p2 x2) /\
(forall k, 2 <= k < r ->
 in_blockA (ablocks B ly S) (wp + 8 * k) 8 /\
 aval_mem (rdW W mem) (wp + 8 * k) 8 (nth (Z.to_nat k) pw 0) /\
 cwc_sblk ly S (rdW W mem) (nth (Z.to_nat k) pw 0) (nth (Z.to_nat k) ws [])) /\
wp mod 8 = 0 /\
nargs = 3 /\ x1 = pf_bytes (pf_dec (r - 2)) /\ x2 = pf_bytes (chain_list_at atoi_a r ws) /\
count_cid 4 (frames S) < fs_frames 4 /\
st_nev S + EV_CHECK_WORDS_CHAIN <= EV_MAX.

(* the conclusion of tcheck_words_chain_spec: the blocks are kept, and the side-stack frame is the only state change
   (the layout is kept, the allocator state up to st_fs); FP-existential (apost_baseF, CmdBase.v), at the section's
   FP state *)
Definition cwc_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md : world SEGS -> config -> Prop :=
apost_baseF SEGS B CHECK_WORDS_CHAIN_STK [] regs ly S W mem md EV_CHECK_WORDS_CHAIN
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\
 ly' = ly /\ exists f, S' = set_fs f S).

(* the allocator state differs from the entry's only in st_fs: the take of the side-stack frame and its release
   are set_fs (aj_stack_malloc_atS, stack_free_state), and no runtime entry the walk calls changes the state. Each
   stage after the take carries it for its S2, and the teardown concludes the post's frame form from it. *)
Definition cwc_frm (S S2 : astate) : Prop := exists f, S2 = set_fs f S.

(* the saved registers, as cgif's cl_frame (lib/A/AChc.v:40-41) *)
Definition cwc_frame (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j rr, nth_error cwc_saved j = Some rr ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 rr))).

(* the spill slots at sp1 that the code reads after the frame setup (written at 0x89128-0x8927c): the shadow of
   list's first byte (24), the frame's first metadata byte (32), the frame as the side-stack entry returned it
   (40) and as the code keeps it (48), the recorded call (56), list (72), read (80) and the shadow base (88). The
   slot at 64 ("%d") is written by the loop's set-up only (0x892a4), so it is the loop's own premise; the slot at
   112 (the frame, 0x8918c) is never read. *)
Definition cwc_spill (m : word -> option byte) (sp1 cp F r : Z) : Prop :=
val_mem SEGS m (sp1 + 24) 8 (SHADOW_OFF + F / 8 + 4) /\
val_mem SEGS m (sp1 + 32) 8 (SHADOW_OFF + F / 8) /\
val_mem SEGS m (sp1 + 40) 8 F /\
val_mem SEGS m (sp1 + 48) 8 F /\
val_mem SEGS m (sp1 + 56) 8 cp /\
val_mem SEGS m (sp1 + 72) 8 (F + OFF_LIST) /\
val_mem SEGS m (sp1 + 80) 8 r /\
val_mem SEGS m (sp1 + 88) 8 SHADOW_OFF.

(* the frame's shadow bytes the setup leaves and the loop and the tail read: list [32, 801) and count [944, 960)
   marked usable *)
Definition cwc_fshadow (rd : reader) (F : Z) : Prop :=
(forall i, 4 <= i < 100 -> rd (SHADOW_OFF + F / 8 + i) = Some 0) /\
rd (SHADOW_OFF + F / 8 + 100) = Some 1 /\
rd (SHADOW_OFF + F / 8 + 118) = Some 0 /\
rd (SHADOW_OFF + F / 8 + 119) = Some 0.

(* what holds at every stage boundary after the take *)
Definition cwc_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md S2 memc mdc (fpos sp1 cp r : Z) : Prop :=
ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(CWC_CID, fpos)] ly S2 W memc mdc 0 /\
ablocks B ly S2 = ablocks B ly S /\
sp1 = 32 * ((spZ regs - 224) / 32) /\
cwc_frame (mrestrict (w_H W) memc) (spZ regs) regs /\
cwc_spill (mrestrict (w_H W) memc) sp1 cp (frame_addr ly CWC_CID fpos) r /\
rdword (rdW W memc) (frame_addr ly CWC_CID fpos + 1016) = Some (flag_addr ly CWC_CID fpos) /\
cwc_fshadow (rdW W memc) (frame_addr ly CWC_CID fpos).

(* a range a wrapper may read (RtDefs' aread_ok without the scratch window) *)
Definition cwc_rd (W : world SEGS) mem (p n : Z) : Prop :=
0 <= p /\ p + n <= alloc_ceiling /\ 0 <= n < 2 ^ 32 /\
(forall a, p <= a < p + n -> rdW W mem a <> None) /\
amem_range p n /\
range_addressable (rdW W mem) SHADOW_OFF p n /\
(0 < n -> shadow_hull_vis (rdW W mem) p n).

(* a C string a wrapper may read *)
Definition cwc_strk (W : world SEGS) mem (p : Z) (x : list byte) : Prop :=
0 < p /\ astr_at SEGS W mem p x /\ cwc_rd W mem p (astr_len x + 1) /\ atail_vis SEGS W mem (p + astr_len x).

(* slot j of the harness's word array: the pointer it holds and its shadow byte (the inline check of the loop) *)
Definition cwc_wordk (W : world SEGS) mem (wp j v : Z) : Prop :=
0 <= wp + 8 * j /\ wp + 8 * j + 8 <= alloc_ceiling /\
aval_mem (rdW W mem) (wp + 8 * j) 8 v /\
rdW W mem (SHADOW_OFF + (wp + 8 * j) / 8) = Some 0.

(* --- the stage statements --- *)

(* the teardown and the epilogue, 0x89408 .. ret: s0 = sp0, s1 = sp1; the teardown reloads the frame's metadata
   bytes (sp1 + 32), the shadow of list's first byte (sp1 + 24) and the frame (sp1 + 48, sp1 + 40) from the spill
   slots of cwc_spill *)
Definition CWC_TD_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cp wp r nargs p1 p2 : Z) pw ws x1 x2 S2 memc mdc fpos sp1
  (regsc : bvmap 5 word),
cwc_pre ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 ->
cwc_mid ly S W regs mem md S2 memc mdc fpos sp1 cp r ->
cwc_frm S S2 ->
getr regsc 2 = w64 sp1 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 (spZ regs) -> getr regsc 9 = w64 sp1 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + CWC_TEARDOWN)) memc (seg_rom SEGS)) mdc)
(cwc_post ly S W regs mem md).

(* the tail, 0x89334 .. the teardown: the UBSan check of read - 2, the count text, the UBSan checks and the
   instrumented checks of the recorded call, the two strcmp calls and the abort edge they exclude; list holds the
   whole member text. The tail reloads read (sp1 + 80), the frame (sp1 + 48), the recorded call (sp1 + 56), the
   shadow base (sp1 + 88) and list (sp1 + 72) from the spill slots of cwc_spill *)
Definition CWC_TAIL_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cp wp r nargs p1 p2 : Z) pw ws x1 x2 S2 memc mdc fpos sp1
  (regsc : bvmap 5 word),
cwc_pre ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 ->
cwc_mid ly S W regs mem md S2 memc mdc fpos sp1 cp r ->
cwc_frm S S2 ->
(* rounding mode 0 at this stage's FP state: the snprintf wrapper's frm0_entry *)
frm0 fx ->
getr regsc 2 = w64 sp1 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 (spZ regs) -> getr regsc 9 = w64 sp1 ->
abytes_at SEGS W memc (frame_addr ly CWC_CID fpos + OFF_LIST) (pf_bytes (chain_list_at atoi_a r ws ++ [0])) ->
cwc_strk W memc p1 x1 -> cwc_strk W memc p2 x2 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + CWC_TAIL)) memc (seg_rom SEGS)) mdc)
(cwc_post ly S W regs mem md).

(* the loop, from the head 0x892b4 for word k (2 <= k < read) on: n = read - k iterations are left; s3 = w,
   s4 = k, s6 = w & 7 (0: w mod 8 = 0), s7 = " %d", s8 = s9 = w + 8k, s11 = the length of the text so far; the
   slot at sp1 + 64 holds "%d" (the loop's set-up wrote it). The loop reloads list (sp1 + 72), read (sp1 + 80)
   and the shadow base (sp1 + 88) from the spill slots of cwc_spill *)
Definition CWC_LOOP_stmt : Prop :=
forall (n : nat) ly S W (regs : bvmap 5 word) mem md ch (cp wp r nargs p1 p2 : Z) pw ws x1 x2 S2 memc mdc fpos sp1
  (regsc : bvmap 5 word) (k : Z),
cwc_pre ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 ->
cwc_mid ly S W regs mem md S2 memc mdc fpos sp1 cp r ->
cwc_frm S S2 ->
(* rounding mode 0 at this stage's FP state: the snprintf wrapper's frm0_entry *)
frm0 fx ->
Z.of_nat n = r - k -> 2 <= k < r ->
getr regsc 2 = w64 sp1 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 (spZ regs) -> getr regsc 9 = w64 sp1 ->
getr regsc 19 = w64 wp -> getr regsc 20 = w64 k -> getr regsc 22 = w64 0 ->
getr regsc 23 = w64 A_FMT_SPD ->
getr regsc 24 = w64 (wp + 8 * k) -> getr regsc 25 = w64 (wp + 8 * k) ->
getr regsc 27 = w64 (Z.of_nat (length (cwc_T ws k))) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 64) 8 A_FMT_D ->
abytes_at SEGS W memc (frame_addr ly CWC_CID fpos + OFF_LIST) (pf_bytes (cwc_T ws k ++ [0])) ->
(forall j, k <= j < r -> cwc_wordk W memc wp j (nth (Z.to_nat j) pw 0) /\
  cwc_strk W memc (nth (Z.to_nat j) pw 0) (nth (Z.to_nat j) ws [])) ->
cwc_strk W memc p1 x1 -> cwc_strk W memc p2 x2 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + CWC_LOOP)) memc (seg_rom SEGS)) mdc)
(cwc_post ly S W regs mem md).

(* --- what every stage uses of the definitions above --- *)

Lemma cwc_aread_of_rd : forall stk W (regs : bvmap 5 word) mem p n,
cwc_rd W mem p n -> alloc_ceiling <= spZ regs - stk -> aread_ok SEGS stk W regs mem p n.
Proof.
intros stk W regs mem p n (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hs.
split; [exact H0|]. pose proof asan_consts as (C1 & _). split; [lia|]. split; [exact H2|]. split.
{ intros a Ha. split; [exact (H3 a Ha)|]. unfold ascratch_stk. lia. }
split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

(* everything below alloc_ceiling that a call leaves alone *)
Definition cwc_kept_below (W : world SEGS) mem mem' (X : Z -> Prop) : Prop :=
forall a, 0 <= a < alloc_ceiling -> ~ X a -> rdW W mem' a = rdW W mem a.

(* the shadow byte of an address below alloc_ceiling, and the shadow word around it, lie in the shadow band *)
Lemma cwc_shadow_band : forall x, 0 <= x < alloc_ceiling ->
SHADOW_OFF <= SHADOW_OFF + x / 8 /\ SHADOW_OFF + x / 8 + 8 < kHighShadowEnd /\
SHADOW_OFF <= (SHADOW_OFF + x / 8) / 8 * 8 /\ (SHADOW_OFF + x / 8) / 8 * 8 <= SHADOW_OFF + x / 8.
Proof.
intros x Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (H0 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H1 : x / 8 < 17592185978880) by (apply Z.div_lt_upper_bound; lia).
assert (H2 : 268431360 <= (SHADOW_OFF + x / 8) / 8) by (apply Z.div_le_lower_bound; unfold SHADOW_OFF; lia).
pose proof (Z.mul_div_le (SHADOW_OFF + x / 8) 8 ltac:(lia)) as H3.
rewrite C2. unfold SHADOW_OFF in *. lia.
Qed.

Lemma cwc_rd_kept : forall W mem mem' (X : Z -> Prop) p n,
cwc_kept_below W mem mem' X ->
(forall a, p <= a < p + n -> ~ X a) ->
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ X s) ->
cwc_rd W mem p n -> cwc_rd W mem' p n.
Proof.
intros W mem mem' X p n HK HX HXs (H0 & H1 & H2 & H3 & H4 & H5 & H6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
{ intros a Ha. rewrite (HK a ltac:(lia) (HX a Ha)). exact (H3 a Ha). }
split; [exact H4|]. split.
- intros x Hx. destruct (H5 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. pose proof (cwc_shadow_band x ltac:(lia)) as (B1 & B2 & _).
  rewrite (HK (SHADOW_OFF + x / 8) ltac:(unfold SHADOW_OFF in *; lia) ltac:(apply HXs; lia)). exact Hs.
- intros Hn s Hs. pose proof (H6 Hn s Hs) as Hv. unfold shadow_addr in Hs.
  pose proof (cwc_shadow_band p ltac:(lia)) as (B1 & B2 & B3 & B4).
  pose proof (cwc_shadow_band (p + n - 1) ltac:(lia)) as (D1 & D2 & D3 & D4).
  assert (Hs0 : SHADOW_OFF <= s < kHighShadowEnd) by lia.
  rewrite (HK s ltac:(unfold SHADOW_OFF in *; lia) (HXs s Hs0)). exact Hv.
Qed.

Lemma cwc_strk_kept : forall W mem mem' (X : Z -> Prop) p x,
cwc_kept_below W mem mem' X ->
(forall a, p <= a < p + astr_len x + 8 -> ~ X a) ->
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ X s) ->
cwc_strk W mem p x -> cwc_strk W mem' p x.
Proof.
intros W mem mem' X p x HK HX HXs (Hp & Hs & Hr & Ht).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ASAN_CEIL_range) as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
assert (Hl : 0 <= astr_len x) by (unfold astr_len; lia).
pose proof Hr as (R0 & R1 & _).
split; [exact Hp|]. split; [|split; [|]].
- destruct Hs as [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi. unfold astr_len in *.
  rewrite (HK (p + Z.of_nat i) ltac:(lia) ltac:(apply HX; lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
- apply (cwc_rd_kept W mem mem' X p (astr_len x + 1) HK); [intros a Ha; apply HX; lia | exact HXs | exact Hr].
- intros a Ha. pose proof (Z.mod_pos_bound (p + astr_len x) 8 ltac:(lia)).
  assert (Htb : 0 <= p + astr_len x < alloc_ceiling) by lia.
  pose proof (tail_below (p + astr_len x) _ Htb CE2).
  rewrite (HK a ltac:(lia) ltac:(apply HX; lia)). exact (Ht a Ha).
Qed.

Lemma cwc_wordk_kept : forall W mem mem' (X : Z -> Prop) wp j v,
cwc_kept_below W mem mem' X ->
(forall a, wp + 8 * j <= a < wp + 8 * j + 8 -> ~ X a) ->
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ X s) ->
cwc_wordk W mem wp j v -> cwc_wordk W mem' wp j v.
Proof.
intros W mem mem' X wp j v HK HX HXs (H0 & H1 & H2 & H3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact H0|]. split; [exact H1|]. split.
- intros i Hi. rewrite (HK (wp + 8 * j + Z.of_nat i) ltac:(lia) ltac:(apply HX; lia)). exact (H2 i Hi).
- pose proof (cwc_shadow_band (wp + 8 * j) ltac:(lia)) as (B1 & B2 & _).
  rewrite (HK (SHADOW_OFF + (wp + 8 * j) / 8) ltac:(unfold SHADOW_OFF in *; lia) ltac:(apply HXs; lia)). exact H3.
Qed.

Section f.
Hypothesis HR : CwcRec.

(* the statement's read-only premise, carried by the journal's image clause to a later state of the walk *)
Lemma cwc_arodata_now : forall STK sp0 ly S W mem md own lyc Sc (W' : world SEGS) mem' md' k,
arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B STK sp0 [] ly S W mem md own lyc Sc W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 ly S W mem md own lyc Sc W' mem' md' k HRO HJ a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a).
- exact (HRO a Hro Ho He).
- destruct Hro as [(sg & Hin & _ & Hr) | Hrel];
  [exists sg; split; [exact Hin | exact Hr] | exact (cr_relro_img HR a Hrel)].
- exact Ho.
- exact He.
- apply fp_spares_closed; [intros (x & [] & _) | intros X; exact (inFP_nil a X)].
Qed.

(* the read-only words the runtime entries read, at a later state of the walk (check_words_add's cwa_rom_at) *)
Lemma cwc_rom_now : forall STK sp0 ly S W mem md own lyc Sc (W' : world SEGS) mem' md' k,
arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B STK sp0 [] ly S W mem md own lyc Sc W' mem' md' k ->
rt_rom_view SEGS B W' mem'.
Proof.
intros STK sp0 ly S W mem md own lyc Sc W' mem' md' k HRO HJ a Hrom Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a).
- apply HRO; [left; exact Hrom | exact Ho | exact He].
- destruct Hrom as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr].
- exact Ho.
- exact He.
- apply fp_spares_closed; [intros (x & [] & _) | intros X; exact (inFP_nil a X)].
Qed.

(* one format literal at a later state of the walk, as the snprintf contract takes it *)
Lemma cwc_lit_now : forall STK sp0 ly S W mem md own lyc Sc (W' : world SEGS) mem' md' k a (l : list Z) n,
ajournal SEGS B STK sp0 [] ly S W mem md own lyc Sc W' mem' md' k ->
abytes_atR (rdW W mem) a (pf_bytes (l ++ [0])) -> Z.of_nat (length l) = n ->
(forall i, 0 <= i < n + 1 -> in_img SEGS (a + i) /\ ~ Exists (in_zr (a + i)) (as_owned_static B) /\
  ~ (as_errno B <= a + i < as_errno B + 4)) ->
Forall (fun c => 0 < c < 256) l ->
0 < a -> a + n + 1 <= kLowMemEnd - 1 ->
range_addressable (rdW W' mem') SHADOW_OFF a (n + 1) -> shadow_hull_vis (rdW W' mem') a (n + 1) ->
atail_vis SEGS W' mem' (a + n) ->
cwc_strk W' mem' a (pf_bytes l).
Proof.
intros STK sp0 ly S W mem md own lyc Sc W' mem' md' k a l n HJ HB Hn Himg Hnz Ha Hlo Hra Hhull Ht.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HL : astr_len (pf_bytes l) = n) by (unfold astr_len; rewrite pf_bytes_len; exact Hn).
assert (HK : forall i, 0 <= i < n + 1 -> rdW W' mem' (a + i) = rdW W mem (a + i)).
{ intros i Hi. destruct (Himg i Hi) as (H1 & H2 & H3). apply (F3 (a + i) H1 H2 H3).
  apply fp_spares_closed; [intros (x & [] & _) | intros X; exact (inFP_nil _ X)]. }
assert (HB' : abytes_atR (rdW W' mem') a (pf_bytes (l ++ [0]))).
{ intros i Hi. rewrite pf_bytes_len, length_app in Hi. cbn [length] in Hi.
  rewrite (HK (Z.of_nat i)) by lia. exact (HB i ltac:(rewrite pf_bytes_len, length_app; cbn [length]; lia)). }
split; [lia|]. split; [|split; [|rewrite HL; exact Ht]].
- split.
  + apply abytes_atR_view. rewrite <- pf_bytes_nul. exact HB'.
  + intros Hin. unfold pf_bytes in Hin. apply in_map_iff in Hin as (c & Hc & Hin).
    rewrite Forall_forall in Hnz. pose proof (Hnz c Hin) as Hc0.
    apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc.
    change (bv_modulus 8) with 256 in Hc. rewrite Z.mod_small in Hc by lia. cbv in Hc. lia.
- rewrite HL. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros b Hb. specialize (HB' (Z.to_nat (b - a)) ltac:(rewrite pf_bytes_len, length_app; cbn [length]; lia)).
    replace (a + Z.of_nat (Z.to_nat (b - a))) with b in HB' by lia. rewrite HB'. discriminate. }
  split; [unfold amem_range; left; lia|]. split; [exact Hra | intros _; exact Hhull].
Qed.

(* the two format literals at a later state of the walk *)
Lemma cwc_fmt_now : forall STK sp0 ly S W mem md own lyc Sc (W' : world SEGS) mem' md' k,
cmd_ro_ok (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B STK sp0 [] ly S W mem md own lyc Sc W' mem' md' k ->
cwc_strk W' mem' A_FMT_D (pf_bytes [37; 100]) /\ cwc_strk W' mem' A_FMT_SPD (pf_bytes [32; 37; 100]).
Proof.
intros STK sp0 ly S W mem md own lyc Sc W' mem' md' k HRO HAO HJ.
pose proof HJ as (HAR' & _).
destruct (cr_lit_tail HR lyc Sc W' mem' md' HAR') as [T1 T2].
destruct (cr_lit_ra HR _ _ _ _ _ HAR') as (R1 & H1 & R2 & H2).
pose proof (cr_lit_ro HR) as LRO.
destruct HRO as [HB _]. unfold cmd_ro_bytes in HB.
assert (B1 : abytes_atR (rdW W mem) 0x218e0 RO_lit_218e0)
by (repeat match type of HB with _ /\ _ => destruct HB as [? HB] end; assumption).
assert (B2 : abytes_atR (rdW W mem) 0x21b80 RO_lit_21b80)
by (repeat match type of HB with _ /\ _ => destruct HB as [? HB] end; assumption).
unfold A_FMT_D, A_FMT_SPD, LEN_FMT_D, LEN_FMT_SPD in *.
split.
- apply (cwc_lit_now STK sp0 ly S W mem md own lyc Sc W' mem' md' k 0x218e0 [37; 100] 2 HJ B1 eq_refl);
  [ intros i Hi; apply LRO; lia | repeat constructor; lia | lia | unfold kLowMemEnd; lia
  | exact R1 | exact H1 | exact T1 ].
- apply (cwc_lit_now STK sp0 ly S W mem md own lyc Sc W' mem' md' k 0x21b80 [32; 37; 100] 3 HJ B2 eq_refl);
  [ intros i Hi; apply LRO; lia | repeat constructor; lia | lia | unfold kLowMemEnd; lia
  | exact R2 | exact H2 | exact T2 ].
Qed.

End f.

End e.
End c.
End b.

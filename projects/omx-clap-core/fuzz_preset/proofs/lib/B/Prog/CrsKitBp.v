(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 755 of its 825 lines of code are new or changed and 444 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): the KIT of the walk of check_reject_clean_starved against the kit's
   text tcheck_reject_clean_starved_specX. This file STATES the walk at B': the stage record, the text's pre and post,
   the boundary pcs, the stage invariants, the register sets and one continuation predicate per segment entry. The
   segment files prove the segments; the composition composes them backwards from R.
   rule 24: proves no function (kind: statement + continuation predicates + kit lemmas). Reuse search: two independent
   runs of `proof-index check_reject_clean_starved`, CONFIRMED by the checker LookupCheckCrcsAp. At that search
   origin/ossv/recipes had no lib/A or lib/B, its released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only,
   and no released asan Proof.v existed for check_reject_clean_starved.
   DONOR (rule 24, reuse): the A' kit lib/A/Prog/CrsKitAp.v blob 3c2dbff7608c (a working branch commit
   99a2cf39788b, kit v3.2). Its design is carried over NAME FOR NAME with a `_B` suffix: Sections d / f over B / ARx /
   LAWS, the stage record (fields `cb_*` here), crs_pre / crs_post, crs_cfg / crs_regsat, the saved-slot, frame, slot,
   live, data and tree invariants, crs_from_<SEG>, CrsKeep, and the kit lemmas. Every pc, slot, instruction word,
   register list and invariant below is RE-DERIVED at B': measured on the B' listing of record and on the unstripped
   twin, never shifted from an A' number.
   INPUTS.
   - Pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
     unstripped twin reports/preset-harness/bound-fix/9e1283d1/unstripped/fuzz_preset/fuzz_preset.asan-ubsan, ELF
     sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175 (the ELF PRH_ImgB.v was generated from).
   - Listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (a Theorem Labs lane's listings v3,
     carried by int102). Entry 0x820e0 = slot 645 (B_entry_check_reject_clean_starved), 285 slots (645..929, the
     last one the UBSan trap; slot 930 is read_members' entry 0x82554).
   - Image record lib/B/PRH_ImgB.v blob 3216eca68342 (prh_img_B).
   - The kit text: tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v blob 9ecd8eb167c6, with lib/A/PRH_Base.v blob
      fdb45545469b: the kit's texts, whose whole lib/A/PRH_*.v set and
     lib/Spec/*.v set are on this branch by path. The spec text itself is CHARACTER FOR CHARACTER the decff67d721f text
     the A' kit proves (blob 4cb899514e6c); what f97c changed under it is listed below.
   WHAT f97c CHANGED UNDER THE DONOR'S PREDICATES (every A' predicate whose B' twin had to follow):
   - fpre (PRH_Base.v) gained `frm_zero (@YK11.fp_csr fx)` as its last conjunct (FRM0-ENTRY: callers supply the
     entry rounding mode). crs_pre_B's FIRST conjunct is that fpre, so the entry rounding mode now comes twice: once
     inside fpre and once as the text's own last premise ck_frm0. Both are kept, in the text's order and spelling.
     No other predicate of this kit changed: ck_crcs_evs / ck_crcs_growth / ck_crcs_max / ck_pick / ck_djb2 / ck_read /
     ck_tree_ok / ck_ncalls / RQ_crcs / LIVE_check_reject_clean_starved / FR_check_reject_clean_starved /
     ck_FRAMES_CAP / RQW / prh_ledger / prh_run_at / bytes_at / src_rd / prhReader_home / RQ_pj_parse are the decff
     texts unchanged (src_rd and PRH_Base's header gained comments only).
   - LANE-VISIBLE, KIT UNCHANGED: tfuzz_free_specX's room conjunct is now under `p <> 0` (crs_room_evs_of_run_B's two
     nth_error facts are what that arm takes, as before); the reader-side pj_free is keyed on pj_frees (PJF-TIE);
     ck_crcs_evs_supply is Qed; PRH_NamesCheck is a build step of the kit's set, as PRH_ElabCheck was (in the released file lib/A/PRH_ElabCheck.v, deleted in this series).
   THE B' BODY AGAINST THE A' BODY (measured: capstone over the twin, the B' listing, and the A' cut list of
   the internal file SEGMENT-PLAN-Aprime.md). Same ten segments and the same exits; three differences:
   (a) the COMPACT injected write's pick is OUT OF LINE: `jal fuzz_pick` at +1068, its return site +1072. On A' the
       third djb2 loop L3 is inlined there (A' +1056..+1100) and eats s4 / s5. So B' H3 ends in a CALL (the kit's
       tfuzz_pick_specX, whose value is ck_pick - already inside ck_crcs_growth / ck_crcs_max, so the post is the
       same), B' X3 begins with the pick in a0 (A': a0 = the count, a2 = the hash), s4 / s5 are still live at B' X3
       and B' has two inlined loops, not three (pi_err_sites has two entries, not three).
   (b) UBSAN (this image is asan-ubsan, A' is asan): each inlined loop carries three pointer-overflow checks per
       iteration (L1 +332 / +344 / +348, L2 +576 / +588 / +592), all branching to the UBSan trap `unimp` at +1136.
       Those six arms are REFUTED by crs_pre_B's `0 < cb_data C` and `cb_data C + cSize_B C < 2 ^ 62` (the loop's back
       edge re-enters at the first check: B' L1 +396 jumps to +332, L2 +640 to +576).
   (c) the five ran-out reads are `lbu a0, -1340(s8)` with s8 the auipc value of +476 (A': +540 from the auipc of
       +452); the displacement is NEGATIVE here (CRS_OFF_OWN_B), so CRS_RO_B lies ABOVE g_own_ran_out.
   THE CUT, with the A' -> B' map. Offsets are from the entry, each 4 * a slot of the B' listing (crs_slots_B /
   crs_listing_cut_B check them against the listing; crs_pcs_plan_B is the one place the addresses are written):
     seg    B' off  B' pc     slot | A' off  A' pc    | what
     E      +0      0x820e0   645  | +0      0x82160  | prologue, the use-after-return word, __asan_stack_malloc_1
                                   |                  | (+120), frame header, the sixteen shadow pokes, fuzz_alloc_live
     H1     +296    0x82208   719  | +296    0x82288  | `mv s6, a0`; beqz took; the djb2 loop L1 (+332 .. +396, with
                                   |                  | its UBSan checks and its per-byte ASan check)
     X1     +416    0x82280   749  | +392    0x822e8  | s8 = the local; fuzz_alloc_fail (h % took); pj_parse;
                                   |                  | fuzz_alloc_fail (-1); check_reject_clean; beqz doc (+472) -> R
     W1     +476    0x822bc   764  | +452    0x82324  | own check #1 (+480 / +484), fuzz_alloc_ran_out; count;
                                   |                  | pj_write (doc, 1); fuzz_free; count; count == before (+524) -> R
     H2     +528    0x822f0   777  | +504    0x82358  | own check #2 (+528 / +532), fuzz_alloc_ran_out; count; loop L2
     X2     +664    0x82378   811  | +616    0x823c8  | fail (h % (count - k)); pj_write (doc, 1); fail (-1); own
                                   |                  | check #3 (+712 / +716), ran_out -> F, else -> Z
     F      +728    0x823b8   827  | +680    0x82408  | fuzz_free (s7)
     R      +736    0x823c0   829  | +688    0x82410  | frame retire, the fake frame's release, restores, ret
     Z      +992    0x824c0   893  | +944    0x82510  | bnez s7 -> ABORT; live != s6 -> ABORT; count; pj_write
                                   |                  | (doc, 0); fuzz_free; count; count == before (+1032) -> R; own
                                   |                  | check #4 (+1036 / +1040), ran_out -> R
     H3     +1052   0x824fc   908  | +1004   0x8254c  | count; `sub a2, a0, s7` (= N0); fuzz_pick (data, size, N0) at
                                   |                  | +1068 (A': the inlined loop L3)
     X3     +1072   0x82510   913  | +1092   0x825a4  | fail (the pick); pj_write (doc, 0); fail (-1); own check #5
                                   |                  | (+1100 / +1104), ran_out -> F; s7 != 0 -> ABORT; live == s6 -> R
     ABORT  +1128   0x82548   927  | +1168   0x825f0  | __asan_handle_no_return + abort; UNREACHABLE
     UNIMP  +1136   0x82550   929  | -                | the UBSan trap of the two loops (B' only)
     SMALLOC+120    0x82158   675  | +120    0x821d8  | `jal __asan_stack_malloc_1` (class 1, 128 bytes)
     PICK   +1068   0x8250c   912  | -                | `jal fuzz_pick` (B' only; inlined on A')
     own    +484 / +532 / +716 / +1040 / +1104       | A': +460 / +508 / +668 / +992 / +1144 | the five `bnez a0`
     err    +412 / +660                              | A': +388 / +612 / +1088               | the report arms
   H1's took = 0 arm (beqz s7 at +300) jumps to X1's LAST instruction, beqz doc at +472; H1's lane runs that one
   instruction too and exits to R (doc = 0) or W1 (doc <> 0).
   The count == before arms (+524, +1032) are refuted, not taken: a whole write makes at least one call
   (crs_wcalls_pos_B, crs_kfull_B). The two `__asan_report_load1` arms (+412, +660 = pi_err_sites) are refuted by
   PRW_CrcGen.djb_byte_shadow (the data is addressable, crs_dat_B); the six UBSan arms as in (b) above.
   THE RAN-OUT CHECKS. Each of the five checks is `lbu a0, -1340(s8)` (s8 the auipc value of +476; at check #1 the
   listing's PLdHi of the object atom 13 through the hi atom 17) then `bnez a0` (the OWN arm), then fuzz_alloc_ran_out
   and `bnez a0` (the RAN arm; its value is the ledger's g_ran_out, so ran = 1 on it). Both arms go to R (checks #1,
   #2, #4) or F (checks #3, #5); crs_from_R_B / crs_from_F_B ask the counter facts crs_post_B needs (crs_cnt_end_B).
   THE OWN ARMS ARE REFUTED: at each check the lbu reads g_own_ran_out, which the boundary's ledger holds at 0
   (prh_ledger_own, PRH_Base.v), so the `bnez a0` at +484 / +532 / +716 / +1040 / +1104 is not taken; the cell is kept
   across the callees before each read by their own texts' ledgers.
   KIT v3 (the kit's E sweep), as in the donor: the entry ledger is `prh_ledger .. SIZE_MAXZ ran most 0` and the post's is
   `.. ran' most 0`; every boundary's ledger (crs_core_B) is `.. ran3 (cb_most C) 0`. crs_post_B is the text's post
   exactly, so the segments prove it directly. The entry premise prh_run_at .. rp_i (ck_crcs_evs ..) is in crs_pre_B;
   the post's position is EXACT under ran' = 0, and so is every boundary's (crs_pos_B over that boundary's consumed
   prefix crs_evs_at_<SEG>_B). After a REFUSAL (ran3 = 1) no position of the model's run describes the state (the
   text's own note), so none is stated.
   NUMERALS. Register numbers 1, 2, 3, 4, 8 .. 27 and 10 .. 13 are RISC-V names (s0 = 8, s1 = 9, s2 = 18 .. s11 = 27).
   The offsets above are LENGTHs (4 * slot). 128 (the `addi sp, sp, -128` frame and the class-1 fake frame), 32 (the
   realignment, and the struct pj local's offset), 56 (sizeof (struct pj)), -1340 (the lbu's signed displacement
   -0x53c, read off the listing word 0xac4c4503) are LENGTHs of the B' listing; 1 is the frame class
   __asan_stack_malloc_1 names; 2 ^ 24 and 2 ^ 62 are DERIVED (the kit's bounds); 645 and the slot numbers are the B'
   listing's. Address literals appear ONLY in the computation lemmas that check the cut against the image
   (crs_entry_B, crs_pcs_plan_B); instruction words appear only in crs_listing_cut_B / crs_frame_class_B /
   crs_listing_own_B. Every definition reads B_prog_sigma / B_prog_base / pa_val or a PrhImg field of prh_img_B. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- the boundary pcs, as offsets from B_prog_base (DERIVED from the entry; no ADDRESS literal) ---- *)
Definition CRS_PC0_B : Z := B_prog_sigma AS_check_reject_clean_starved - B_prog_base.
Definition CRS_PC_E_B : Z := CRS_PC0_B.
Definition CRS_PC_H1_B : Z := CRS_PC0_B + 296.
Definition CRS_PC_X1_B : Z := CRS_PC0_B + 416.
Definition CRS_PC_W1_B : Z := CRS_PC0_B + 476.
Definition CRS_PC_H2_B : Z := CRS_PC0_B + 528.
Definition CRS_PC_X2_B : Z := CRS_PC0_B + 664.
Definition CRS_PC_F_B : Z := CRS_PC0_B + 728.
Definition CRS_PC_R_B : Z := CRS_PC0_B + 736.
Definition CRS_PC_Z_B : Z := CRS_PC0_B + 992.
Definition CRS_PC_H3_B : Z := CRS_PC0_B + 1052.
Definition CRS_PC_X3_B : Z := CRS_PC0_B + 1072.
Definition CRS_PC_ABORT_B : Z := CRS_PC0_B + 1128.
(* the UBSan trap the two inlined loops branch to (B' only), and the out-of-line pick of the compact write *)
Definition CRS_PC_UNIMP_B : Z := CRS_PC0_B + 1136.
Definition CRS_PC_PICK_B : Z := CRS_PC0_B + 1068.
(* the stack_malloc call and the five own checks' `bnez a0` (refuted from the ledger's own cell, header) *)
Definition CRS_PC_SMALLOC_B : Z := CRS_PC0_B + 120.
Definition CRS_PC_OWN1_B : Z := CRS_PC0_B + 484.
Definition CRS_PC_OWN2_B : Z := CRS_PC0_B + 532.
Definition CRS_PC_OWN3_B : Z := CRS_PC0_B + 716.
Definition CRS_PC_OWN4_B : Z := CRS_PC0_B + 1040.
Definition CRS_PC_OWN5_B : Z := CRS_PC0_B + 1104.

(* the fake frame: __asan_stack_malloc_1 (class 1, 128 bytes), the struct pj local at + 32 *)
Definition CRS_CID_B : Z := 1.
Definition CRS_OFF_DOC_B : Z := 32.
(* the own checks' `lbu a0, -1340(s8)` (the listing word 0xac4c4503; NEGATIVE on B') *)
Definition CRS_OFF_OWN_B : Z := -1340.

(* ---- computation: the entry, the slots, the frame, the class ---- *)
Lemma crs_entry_B : B_prog_sigma AS_check_reject_clean_starved = 0x820e0 /\
  B_prog_slot AS_check_reject_clean_starved = 645%nat.
Proof. exact B_entry_check_reject_clean_starved. Qed.

Lemma crs_slots_B :
  Z.to_nat (CRS_PC_E_B / 4) = 645%nat /\ Z.to_nat (CRS_PC_H1_B / 4) = 719%nat /\
  Z.to_nat (CRS_PC_X1_B / 4) = 749%nat /\ Z.to_nat (CRS_PC_W1_B / 4) = 764%nat /\
  Z.to_nat (CRS_PC_H2_B / 4) = 777%nat /\ Z.to_nat (CRS_PC_X2_B / 4) = 811%nat /\
  Z.to_nat (CRS_PC_F_B / 4) = 827%nat /\ Z.to_nat (CRS_PC_R_B / 4) = 829%nat /\
  Z.to_nat (CRS_PC_Z_B / 4) = 893%nat /\ Z.to_nat (CRS_PC_H3_B / 4) = 908%nat /\
  Z.to_nat (CRS_PC_X3_B / 4) = 913%nat /\ Z.to_nat (CRS_PC_ABORT_B / 4) = 927%nat /\
  Z.to_nat (CRS_PC_UNIMP_B / 4) = 929%nat /\ Z.to_nat (CRS_PC_PICK_B / 4) = 912%nat /\
  Z.to_nat (CRS_PC_SMALLOC_B / 4) = 675%nat.
Proof. vm_compute. repeat split. Qed.

(* the listing entry at each boundary (the cut is on the listing the engine runs) *)
Lemma crs_listing_cut_B :
  nth_error B_prog_listing (Z.to_nat (CRS_PC_E_B / 4)) = Some (PW 0xf8010113) /\        (* addi sp, sp, -128 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_H1_B / 4)) = Some (PW 0x50b13) /\          (* mv s6, a0 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_X1_B / 4)) = Some (PW 0x20d0c13) /\        (* addi s8, s10, 32 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_W1_B / 4)) = Some (PHi (24%bv : bv 5) 17%nat) /\  (* auipc s8 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_H2_B / 4)) = Some (PW 0xac4c4503) /\       (* lbu a0, -1340(s8) *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_X2_B / 4)) = Some (PW 0x1751663) /\        (* bne a0, s7, 12 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_F_B / 4)) = Some (PW 0xb8513) /\           (* mv a0, s7 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_R_B / 4)) = Some (PW 0xff800513) /\        (* li a0, -8 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_Z_B / 4)) = Some (PW 0x80b9463) /\         (* bnez s7 *)
  nth_error B_prog_listing (Z.to_nat (CRS_PC_H3_B / 4)) = Some (PCall AS_fuzz_alloc_count (1%bv : bv 5)) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_PICK_B / 4)) = Some (PCall AS_fuzz_pick (1%bv : bv 5)) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_X3_B / 4)) = Some (PCall AS_fuzz_alloc_fail (1%bv : bv 5)) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_ABORT_B / 4)) = Some (PCall AS___asan_handle_no_return (1%bv : bv 5)) /\
  nth_error B_prog_listing (S (Z.to_nat (CRS_PC_ABORT_B / 4))) = Some (PCall AS_abort (1%bv : bv 5)) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_UNIMP_B / 4)) = Some (PW 0xc0001073).      (* unimp (UBSan) *)
Proof. vm_compute. repeat split. Qed.

(* the frame: `addi a0, zero, 128` then `jal __asan_stack_malloc_1` (class 1), whose frame is 128 bytes *)
Lemma crs_frame_class_B :
  nth_error B_prog_listing (Z.to_nat (CRS_PC_SMALLOC_B / 4 - 1)) = Some (PW 0x8000513) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_SMALLOC_B / 4)) = Some (PCall AS___asan_stack_malloc_1 (1%bv : bv 5)) /\
  CRS_CID_B = 1 /\ fs_frame_bytes CRS_CID_B = 128.
Proof. vm_compute. repeat split. Qed.

(* the five own reads: check #1 is the listing's PLdHi of the object atom 13 through the hi atom 17 (s8); the
   other four read -1340(s8) *)
Lemma crs_listing_own_B :
  nth_error B_prog_listing (S (Z.to_nat (CRS_PC_W1_B / 4))) =
    Some (PLdHi (10%bv : bv 5) (24%bv : bv 5) 17%nat (A_OBJ 13) 0 SZ1 false) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_OWN2_B / 4 - 1)) = Some (PW 0xac4c4503) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_OWN3_B / 4 - 1)) = Some (PW 0xac4c4503) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_OWN4_B / 4 - 1)) = Some (PW 0xac4c4503) /\
  nth_error B_prog_listing (Z.to_nat (CRS_PC_OWN5_B / 4 - 1)) = Some (PW 0xac4c4503) /\
  CRS_PC_OWN1_B = CRS_PC_W1_B + 8 /\ CRS_PC_OWN2_B = CRS_PC_H2_B + 4.
Proof. vm_compute. repeat split. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

(* s8 from W1 on: the auipc value, g_own_ran_out less the lbu's (negative) displacement *)
Definition CRS_RO_B : Z := @pi_g_own_ran_out prh_img_B - CRS_OFF_OWN_B.
Definition CRS_FRAME_B : Z := @pi_frame prh_img_B F_check_reject_clean_starved.

(* ---- computation: the cut against the image ---- *)
Lemma crs_pc_entry_B : BASE + CRS_PC_E_B = SIGMA AS_check_reject_clean_starved.
Proof. vm_compute. reflexivity. Qed.
Lemma crs_pc_abort_is_pi_B : BASE + CRS_PC_ABORT_B = @pi_abort prh_img_B F_check_reject_clean_starved.
Proof. vm_compute. reflexivity. Qed.
(* pi_frame = 128 + the realignment slack 32 - 16 *)
Lemma crs_frame_is_pi_B : CRS_FRAME_B = 128 + 32 - 16.
Proof. vm_compute. reflexivity. Qed.
(* the TWO report arms are the generated error sites (A' has three: its third loop is inlined) *)
Lemma crs_err_sites_B : @pi_err_sites prh_img_B F_check_reject_clean_starved =
  [BASE + CRS_PC0_B + 412; BASE + CRS_PC0_B + 660].
Proof. vm_compute. reflexivity. Qed.
(* H1 is fuzz_alloc_live's first return site, R is the fuzz_free return site of F, X3 is fuzz_pick's (B' only) *)
Lemma crs_pc_H1_ret_B : In (BASE + CRS_PC_H1_B)
  (@pi_call_rets prh_img_B F_check_reject_clean_starved F_fuzz_alloc_live).
Proof. vm_compute. left. reflexivity. Qed.
Lemma crs_pc_R_ret_B : In (BASE + CRS_PC_R_B)
  (@pi_call_rets prh_img_B F_check_reject_clean_starved F_fuzz_free).
Proof. vm_compute. right. left. reflexivity. Qed.
Lemma crs_pc_X3_ret_B : In (BASE + CRS_PC_X3_B)
  (@pi_call_rets prh_img_B F_check_reject_clean_starved F_fuzz_pick).
Proof. vm_compute. left. reflexivity. Qed.
(* s8: the hi atom 17 is the auipc value, the object atom 13 is g_own_ran_out *)
Lemma crs_ro_atoms_B : VAL (A_HI 17) = CRS_RO_B /\ VAL (A_OBJ 13) = @pi_g_own_ran_out prh_img_B.
Proof. vm_compute. split; reflexivity. Qed.
(* the B' addresses of the cut, the one place they are written *)
Lemma crs_pcs_plan_B :
  BASE + CRS_PC_E_B = 0x820e0 /\ BASE + CRS_PC_H1_B = 0x82208 /\ BASE + CRS_PC_X1_B = 0x82280 /\
  BASE + CRS_PC_W1_B = 0x822bc /\ BASE + CRS_PC_H2_B = 0x822f0 /\ BASE + CRS_PC_X2_B = 0x82378 /\
  BASE + CRS_PC_F_B = 0x823b8 /\ BASE + CRS_PC_R_B = 0x823c0 /\ BASE + CRS_PC_Z_B = 0x824c0 /\
  BASE + CRS_PC_H3_B = 0x824fc /\ BASE + CRS_PC_X3_B = 0x82510 /\ BASE + CRS_PC_ABORT_B = 0x82548 /\
  BASE + CRS_PC_UNIMP_B = 0x82550 /\ BASE + CRS_PC_PICK_B = 0x8250c /\
  BASE + CRS_PC_SMALLOC_B = 0x82158 /\
  BASE + CRS_PC_OWN1_B = 0x822c4 /\ BASE + CRS_PC_OWN2_B = 0x822f4 /\ BASE + CRS_PC_OWN3_B = 0x823ac /\
  BASE + CRS_PC_OWN4_B = 0x824f0 /\ BASE + CRS_PC_OWN5_B = 0x82530 /\
  CRS_RO_B = 0x5de2bc /\ CRS_RO_B + CRS_OFF_OWN_B = 0x5ddd80.
Proof. vm_compute. repeat split. Qed.

(* ---- the list and count arithmetic the boundaries need ---- *)

(* Ledger.lsum under a permutation (the live checks: fuzz_alloc_live = s6) *)
Lemma crs_lsum_perm_B : forall l l', Permutation l l' -> Ledger.lsum l = Ledger.lsum l'.
Proof.
intros l l' H. induction H as [|x l1 l2 H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2].
- reflexivity.
- destruct x as [a k]. cbn [Ledger.lsum]. lia.
- destruct x as [a k]. destruct y as [b m]. cbn [Ledger.lsum]. lia.
- rewrite IH1. exact IH2.
Qed.

Lemma crs_count_le_length_B : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.

(* THE CAPACITY FACT of the E lane: aj_stack_malloc_at_x's `count_cid cid (frames Sc) < fs_frames cid` at cid = 1,
   from the text's frames premise (29 frames at most, against the class's 8192) *)
Lemma crs_cap_B : forall S,
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_reject_clean_starved ->
  count_cid 1 (frames S) < fs_frames 1.
Proof.
intros S H. pose proof (crs_count_le_length_B 1 (frames S)) as Hc.
assert (E1 : ck_FRAMES_CAP - FR_check_reject_clean_starved = 29) by (vm_compute; reflexivity).
assert (E2 : fs_frames 1 = 8192) by (vm_compute; reflexivity).
lia.
Qed.

(* the callees' frame bounds once the function's own frame is pushed: pj_parse's `frames + DOC_D <= fs_frames 0`
   and its ck_FRAMES_CAP - FR_pj_parse, pj_write's `frames < fs_frames 0` *)
Lemma crs_cap_callee_B : forall S S3 pos,
  frames S3 = (CRS_CID_B, pos) :: frames S ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_reject_clean_starved ->
  Z.of_nat (length (frames S3)) <= ck_FRAMES_CAP - FR_pj_parse /\
  Z.of_nat (length (frames S3)) + Z.of_nat DOC_D <= fs_frames 0 /\
  Z.of_nat (length (frames S3)) < fs_frames 0.
Proof.
intros S S3 pos E H. rewrite E. cbn [length].
assert (E1 : ck_FRAMES_CAP - FR_check_reject_clean_starved = 29) by (vm_compute; reflexivity).
assert (E2 : ck_FRAMES_CAP - FR_pj_parse = 30) by (vm_compute; reflexivity).
assert (E3 : Z.of_nat DOC_D = 33) by (vm_compute; reflexivity).
assert (E4 : fs_frames 0 = 16384) by (vm_compute; reflexivity).
lia.
Qed.

(* ======================================================================================================== *)
(* ---- THE WALK'S CONTEXT, ITS PRE AND POST, AND THE BOUNDARIES ---- *)

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* AR_laws_x at the harness head length (YCbqG.v: explicit on the record type) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_B)).

(* THE STAGE RECORD: the text's binders (the model-run position rp_*, the entry state, the input, the tree, the
   ledger and g_most) and the position __asan_stack_malloc_1 returned. The flag reads of the five checks are
   path-local (each arm's register a0), so they are premises of the predicates, not fields. Fields are `cb_*` (the
   A' kit's `c_*`), so a file that takes both kits keeps them apart. *)
Record crsC_B : Type := mkCrsC_B {
  cb_ly : alayout; cb_S : astate; cb_Hp : list Z; cb_W : world SEGS;
  cb_regs : bvmap 5 word; cb_mem : word -> option byte; cb_md : Model; cb_ch : list (Z * Z * Z);
  cb_data : Z; cb_tb : list Z; cb_took : Z; cb_doc : Z; cb_t : PjTree.jv; cb_D : list (Z * Z);
  cb_Lam : list (Z * Z); cb_peak : Z; cb_cnt : Z; cb_ran : Z; cb_most : Z;
  cb_rp_x : list Z; cb_rp_os : list (option nat * option nat * option nat);
  cb_rp_i : nat; cb_rp_H0 : list Z; cb_rp_hist : list YG00.chunk;
  cb_fpos : Z;                         (* the position __asan_stack_malloc_1 returned *)
  (* THE WILD BUDGET OF THE WALK (the kit's cut: the text's post is fpostFbm (wbudget [] (prh_wk F_check_reject_clean_starved))
     because pj_parse's cursor traces are WILD at B' - parse_items' free stores a trace at the cursor end, parse_string's
     at the slot word). The walk keeps every boundary journal at the EMPTY budget, from the entry state with its depot
     replaced by cb_dp (YCbqGwild.ajournal_xw_rebase, at X1 after pj_parse); cb_ws is the budget spent so far, which
     covers the moved depot's wild part from the entry's (crs_dpok_B). R gives the journal back at cb_ws
     (YCbqGwild.ajournal_xw_unbase0). Before X1: cb_dp = the entry depot, cb_ws = []. *)
  cb_dp : list (list Z); cb_ws : list (list Z)
}.

(* the context with the frame position set: the prologue learns cb_fpos only from the frame call, so the E lane
   proves crs_from_E_B C from crs_from_H1_B (crs_with_fpos_B C p) for every p the call may return; the journal's
   entry depot is the entry's own there, at the empty budget *)
Definition crs_with_fpos_B (C : crsC_B) (p : Z) : crsC_B :=
  mkCrsC_B (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_regs C) (cb_mem C) (cb_md C) (cb_ch C) (cb_data C) (cb_tb C)
    (cb_took C) (cb_doc C) (cb_t C) (cb_D C) (cb_Lam C) (cb_peak C) (cb_cnt C) (cb_ran C) (cb_most C)
    (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (cb_rp_H0 C) (cb_rp_hist C) p (st_depot (cb_S C)) [].
(* the context after a rebase: the journal's entry depot moved to d, the budget spent so far ws *)
Definition crs_with_dp_B (C : crsC_B) (d ws : list (list Z)) : crsC_B :=
  mkCrsC_B (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_regs C) (cb_mem C) (cb_md C) (cb_ch C) (cb_data C) (cb_tb C)
    (cb_took C) (cb_doc C) (cb_t C) (cb_D C) (cb_Lam C) (cb_peak C) (cb_cnt C) (cb_ran C) (cb_most C)
    (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (cb_rp_H0 C) (cb_rp_hist C) (cb_fpos C) d ws.

Definition cSize_B (C : crsC_B) : Z := Z.of_nat (length (cb_tb C)).
(* the frame, at the ENTRY layout (alx_layout gives the same address at every later layout of the journal) *)
Definition cF_B (C : crsC_B) : Z := frame_addr (cb_ly C) CRS_CID_B (cb_fpos C).
Definition cOut_B (C : crsC_B) : Z := cF_B C + CRS_OFF_DOC_B.
Definition cHash_B (C : crsC_B) : Z := ck_djb2 5381 (cb_tb C).
Definition cN1_B (C : crsC_B) : Z := PjWriteHyp.wcalls (cb_t C) true.
Definition cN0_B (C : crsC_B) : Z := PjWriteHyp.wcalls (cb_t C) false.
(* the value fuzz_pick returns at the compact injected write (B' only: out of line, the kit's tfuzz_pick_specX) *)
Definition cPick0_B (C : crsC_B) : Z := ck_pick (cb_tb C) (cN0_B C).

(* ---- THE RUN EVENTS (the text's ck_crcs_evs) and their parts, in the order the body makes them: the starved
   reading, then with a tree for p = pretty and p = compact the whole write (w_evs), the fuzz_free of its text
   (w_free), the injected write (w_starved at the model's pick; its chosen failure makes no event). The F site's
   fuzz_free (s7) makes none: s7 = NULL whenever no allocation was refused. Image-free: the same lists as A'. ---- *)
Definition crs_evs_B (C : crsC_B) : list PresetReqAt.hev :=
  ck_crcs_evs ReaderRes.jr_strtod (cb_tb C) (cb_took C) (cb_doc C) (cb_t C).
Definition crs_ev_sp_B (C : crsC_B) : list PresetReqAt.hev :=
  PresetReqAt.starved_parse ReaderRes.jr_strtod (cb_tb C) (Z.to_nat (cb_took C)).
Definition crs_ev_w_B (C : crsC_B) (p : bool) : list PresetReqAt.hev := PresetReqAt.w_evs (cb_t C) p.
Definition crs_ev_wf_B (C : crsC_B) (p : bool) : list PresetReqAt.hev := PresetReqAt.w_free (cb_t C) p.
Definition crs_ev_ws_B (C : crsC_B) (p : bool) : list PresetReqAt.hev :=
  PresetReqAt.w_starved (cb_t C) p (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) p)).
(* the prefix of crs_evs_B consumed at each boundary (when nothing was refused) *)
Definition crs_evs_at_E_B (C : crsC_B) : list PresetReqAt.hev := [].
Definition crs_evs_at_H1_B (C : crsC_B) : list PresetReqAt.hev := [].
Definition crs_evs_at_X1_B (C : crsC_B) : list PresetReqAt.hev := [].
Definition crs_evs_at_W1_B (C : crsC_B) : list PresetReqAt.hev := crs_ev_sp_B C.
Definition crs_evs_at_H2_B (C : crsC_B) : list PresetReqAt.hev :=
  crs_evs_at_W1_B C ++ crs_ev_w_B C true ++ crs_ev_wf_B C true.
Definition crs_evs_at_X2_B (C : crsC_B) : list PresetReqAt.hev := crs_evs_at_H2_B C.
Definition crs_evs_at_Z_B (C : crsC_B) : list PresetReqAt.hev := crs_evs_at_X2_B C ++ crs_ev_ws_B C true.
Definition crs_evs_at_H3_B (C : crsC_B) : list PresetReqAt.hev :=
  crs_evs_at_Z_B C ++ crs_ev_w_B C false ++ crs_ev_wf_B C false.
Definition crs_evs_at_X3_B (C : crsC_B) : list PresetReqAt.hev := crs_evs_at_H3_B C.
Definition crs_evs_at_F_B (C : crsC_B) : list PresetReqAt.hev := crs_evs_B C.
Definition crs_evs_at_R_B (C : crsC_B) : list PresetReqAt.hev := crs_evs_B C.

(* ---- the text's premises (tcheck_reject_clean_starved_specX on the kit's cut 7cdbb61b5fa0, PRH_FnCheck.v:1066-1145), same
   order and spelling; CTX0 is the text's own parameter (the run-word list DW is gone), and the run's strtod model is
   KEYED: ReaderRes.jr_strtod where rp_sm stood, no binder. fpre carries the entry rounding mode since FRM0-ENTRY,
   and the text keeps ck_frm0: both are here, as the text has them. ---- *)
Definition crs_pre_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  fpre B ARx STK (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_regs C) (cb_mem C) (cb_md C) (cb_ch C) /\
  YAkMemnorm.memnorm SEGS (cb_mem C) /\
  prh_univ_closure B CTX0 /\ prh_ctx CTX0 F_check_reject_clean_starved (raZ (cb_regs C) :: spine (cb_ch C)) /\
  getr (cb_regs C) 10 = w64 (cb_data C) /\ getr (cb_regs C) 11 = w64 (cSize_B C) /\
  getr (cb_regs C) 12 = w64 (cb_took C) /\ getr (cb_regs C) 13 = w64 (cb_doc C) /\
  cSize_B C <= 3 * 2 ^ 20 /\ 0 < cb_data C /\ cb_data C + cSize_B C < 2 ^ 62 /\
  src_rd (cb_W C) (cb_mem C) (cb_data C) (cb_tb C) /\
  PRH_FnReader.prhReader_home B (cb_ly C) (cb_S C) (cb_Hp C) (cb_Lam C) (cb_data C) (cSize_B C) /\
  0 <= cb_took C <= ck_ncalls (cb_tb C) /\
  (cb_doc C = 0 \/
   (ck_read (cb_tb C) = Some (cb_t C) /\
    ck_tree_ok (cb_ly C) (cb_S C) (cb_Lam C) (cb_W C) (cb_mem C) (cb_doc C) (cb_t C) (cb_D C) /\
    PjWriteHyp.wlen (cb_t C) false + 1 < 2 ^ 24 /\ PjWriteHyp.wlen (cb_t C) true + 1 < 2 ^ 28 /\
    (PjTree.depth (cb_t C) <= 32)%nat)) /\
  LEDGER (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_Lam C) (cb_peak C) (cb_cnt C) SIZE_MAXZ (cb_ran C)
    (cb_most C) 0 /\
  cb_cnt C < 2 ^ 62 - 2 ^ 30 /\
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (crs_evs_B C) /\
  cb_ran C = 0 /\
  PRH_FnPj.RQ_pj_parse (cb_tb C) <= cb_most C /\
  (cb_doc C <> 0 -> RQW (cb_t C) true <= cb_most C /\ RQW (cb_t C) false <= cb_most C) /\
  blocks_bytes (cb_S C) + LIVE_check_reject_clean_starved (cb_tb C) (cb_t C) <= LIVE_MAX /\
  RQ_crcs (cb_tb C) + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames (cb_S C))) <= ck_FRAMES_CAP - FR_check_reject_clean_starved /\
  room_live_cf (cb_S C) /\
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (cb_rp_H0 C) (cb_rp_hist C) (cb_S C) /\
  ck_frm0 (fx := fx) /\
  (length (cb_rp_os C) <= 4)%nat /\
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_reject_clean_starved) (st_depot (cb_S C)) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (cb_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (cb_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (length (crs_evs_B C)).

(* ---- the text's conclusion, ONE budgeted post (no abort arm), with the EXACT advance under ran' = 0, conjunct for
   conjunct in the text's order. g_most and g_own_ran_out are the ledger's last two arguments: most is kept and the
   own cell ends 0, as at entry. NO REFUSAL (prh_cons_from): ran' = ran. ---- *)
Definition crs_Q_B (C : crsC_B)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    room_live_cf S' /\ exists Lam' peak' cnt' ran',
    Permutation Lam' (cb_Lam C) /\ Permutation (ablocks B ly' S') (ablocks B (cb_ly C) (cb_S C)) /\
    cb_peak C <= peak' /\
    cb_cnt C <= cnt' <= cb_cnt C + ck_crcs_max (cb_tb C) (cb_took C) (cb_doc C) (cb_t C) /\
    (ran' = cb_ran C \/ ran' = 1) /\
    ran' = cb_ran C /\
    (ran' = 0 -> cnt' = cb_cnt C + ck_crcs_growth (cb_tb C) (cb_took C) (cb_doc C) (cb_t C)) /\
    (ran' = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C)
       (cb_rp_i C + length (crs_evs_B C))%nat (cb_rp_H0 C) hist' S') /\
    LEDGER ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' (cb_most C) 0 /\
    PRH_Base.bytes_at W' mem' (cb_data C) (cb_tb C) /\
    (cb_doc C <> 0 -> pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') (cb_doc C) (cb_t C) (cb_D C)).
Definition crs_post_B (C : crsC_B) : world SEGS -> config -> Prop :=
  fpostFbm (fx := fx) B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_reject_clean_starved)) STK [] (cb_regs C)
    (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) (crs_Q_B C).

(* ---- a boundary: the machine state at a pc, its float state fxk (pj_parse's strtod may change it) ---- *)
Definition crs_cfg_B (fxk : YK11.FPState) (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) : config :=
  mkCfg (@YK11.mkst fxk regs (w64 pc) mem (YK11.seg_rom SEGS)) md.
Definition crs_regsat_B (regs : bvmap 5 word) (l : list (bv 5 * Z)) : Prop :=
  Forall (fun p => getr regs (fst p) = w64 (snd p)) l.

(* the journal from entry, with the function's own class-1 frame in `own`, at the EMPTY budget from the entry state
   with its depot moved to cb_dp C (the record's comment) *)
Definition crs_J_B (C : crsC_B) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  AJ STK (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C)
     [(CRS_CID_B, cb_fpos C)] ly3 S3 Hp3 W3 mem3 md3 k.
(* the same journal over a world relation R (the journal's world conjunct is R W W'): crs_J_B is crs_JR_B at wle
   (crs_J_B_R_wle); a cut after a free or a realloc carries crs_JR_B at the re-hiding relation, and crs_JR_B_mono
   moves a journal from a smaller relation to a larger one (wle to wle' by wle_wle') *)
Definition crs_JR_B (R : world SEGS -> world SEGS -> Prop) (C : crsC_B) (ly3 : alayout) (S3 : astate)
  (Hp3 : list Z) (W3 : world SEGS) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  ajournal_xR (SK := SK) SEGS B PST ARx R STK (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C))
    (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(CRS_CID_B, cb_fpos C)] ly3 S3 Hp3 W3 mem3 md3 k.
Lemma crs_J_B_R_wle : forall C ly3 S3 Hp3 W3 mem3 md3 k,
  crs_J_B C ly3 S3 Hp3 W3 mem3 md3 k = crs_JR_B (@wle SEGS) C ly3 S3 Hp3 W3 mem3 md3 k.
Proof. reflexivity. Qed.
Lemma crs_JR_B_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall C ly3 S3 Hp3 W3 mem3 md3 k, crs_JR_B R1 C ly3 S3 Hp3 W3 mem3 md3 k -> crs_JR_B R2 C ly3 S3 Hp3 W3 mem3 md3 k.
Proof.
intros R1 R2 H12 C ly3 S3 Hp3 W3 mem3 md3 k HJ. unfold crs_JR_B, ajournal_xR, ajournal_xwR in *.
exact (ajournal_xbR_mono (SK := SK) SEGS B PST ARx R1 R2 H12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* the moved depot's wild part is covered from the entry's by the budget spent, and that budget is within the text's *)
Definition crs_dpok_B (C : crsC_B) : Prop :=
  YCbqGwild.wbudget [] (prh_wk F_check_reject_clean_starved) (cb_ws C) /\
  incl (wild_part (as_universe B) (cb_dp C)) (wild_part (as_universe B) (st_depot (cb_S C)) ++ cb_ws C).

(* THE THIRTEEN SAVED WORDS: `addi sp, sp, -128`, `sd zero, 0(sp)` (the probe, B' slot 646), then `sd ra, 120(sp)`,
   `sd s0, 112(sp)` .. `sd s11, 24(sp)` (B' slots 647-659); R reads them back from s0 - 128, so a boundary carries
   the SLOTS *)
Definition CRS_SAVED_B : list (Z * bv 5) :=
  [(120, 1%bv); (112, 8%bv); (104, 9%bv); (96, 18%bv); (88, 19%bv); (80, 20%bv); (72, 21%bv);
   (64, 22%bv); (56, 23%bv); (48, 24%bv); (40, 25%bv); (32, 26%bv); (24, 27%bv)].
Definition crs_saved_B (C : crsC_B) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  Forall (fun p : Z * bv 5 =>
            rdword (aview SEGS (w_H W3) mem3) (spZ (cb_regs C) - 128 + fst p)
            = Some (bv_unsigned (getr (cb_regs C) (snd p))))
    CRS_SAVED_B.

(* the frame the prologue holds: pushed on the entry frames, its flag word (R's `ld a0, 120(s2)`, `sb zero, 0(a0)`)
   at the CURRENT layout (aj_flag_store_x's form), its bytes present *)
Definition crs_frame_B (C : crsC_B) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (mem3 : word -> option byte) : Prop :=
  frames S3 = (CRS_CID_B, cb_fpos C) :: frames (cb_S C) /\
  rdword (aview SEGS (w_H W3) mem3) (cF_B C + fs_frame_bytes CRS_CID_B - 8)
    = Some (flag_addr ly3 CRS_CID_B (cb_fpos C)) /\
  (forall a, cF_B C <= a < cF_B C + fs_frame_bytes CRS_CID_B -> apresent (w_H W3) mem3 a).

(* the 56-byte struct pj at F + 32 is unpoisoned: E's sixteen shadow pokes (the `sb` of B' slots 701-717) leave
   shadow [F, F + 32) = f1, [F + 32, F + 88) = 0, [F + 88, F + 128) = f3 *)
Definition crs_slot_B (C : crsC_B) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (cOut_B C) 56 /\
  shadow_hull_vis (aview SEGS (w_H W3) mem3) (cOut_B C) 56.

(* THE MODEL-RUN POSITION AT A BOUNDARY, EXACT: evs is the prefix of crs_evs_B the body has made there
   (crs_evs_at_<SEG>_B). Stated only when nothing was refused (ran3 = 0): after a refusal the instance has freed
   blocks the all-granted run still holds, so no position of the run describes the state. *)
Definition crs_pos_B (C : crsC_B) (evs : list PresetReqAt.hev) (ran3 : Z) (S3 : astate) : Prop :=
  ran3 = 0 -> exists rp_hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C)
    (cb_rp_i C + length evs)%nat (cb_rp_H0 C) rp_hist' S3.

(* the ledger, the counters, the room and the position at a boundary (evs: that boundary's crs_evs_at_<SEG>_B). The
   ran-out cell is the entry's at every boundary (no refusal: prh_cons_from; the injected failures leave it alone) *)
Definition crs_core_B (C : crsC_B) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (Lam3 : list (Z * Z)) (peak3 cnt3 ran3 : Z) (evs : list PresetReqAt.hev) : Prop :=
  LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (cb_most C) 0 /\
  cb_peak C <= peak3 /\ ran3 = cb_ran C /\ cb_cnt C <= cnt3 /\ cnt3 < 2 ^ 62 /\
  room_live_cf S3 /\ crs_pos_B C evs ran3 S3.
(* Lam and the allocator blocks back as they were: the starved reading is refused (it frees its blocks), each whole
   write's text is freed by fuzz_free, each injected write gives NULL and frees its buffer *)
Definition crs_perm_B (C : crsC_B) (ly3 : alayout) (S3 : astate) (Lam3 : list (Z * Z)) : Prop :=
  Permutation Lam3 (cb_Lam C) /\ Permutation (ablocks B ly3 S3) (ablocks B (cb_ly C) (cb_S C)).
Definition crs_live_B (C : crsC_B) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (Lam3 : list (Z * Z)) (peak3 cnt3 ran3 : Z) (evs : list PresetReqAt.hev) : Prop :=
  crs_core_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 ran3 evs /\ crs_perm_B C ly3 S3 Lam3.
(* the input bytes and their shadow (the two hash loops' memory facts, PRW_CrcGen.djb_head, and the fuzz_pick call) *)
Definition crs_dat_B (C : crsC_B) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (Lam3 : list (Z * Z)) : Prop :=
  PRH_Base.bytes_at W3 mem3 (cb_data C) (cb_tb C) /\
  PRH_FnReader.prhReader_home B ly3 S3 Hp3 Lam3 (cb_data C) (cSize_B C) /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (cb_data C) (cSize_B C) /\
  (0 < cSize_B C -> shadow_hull_vis (aview SEGS (w_H W3) mem3) (cb_data C) (cSize_B C)).

(* the document, still the tree the text names *)
Definition crs_tree_B (C : crsC_B) (ly3 : alayout) (S3 : astate) (Lam3 : list (Z * Z)) (W3 : world SEGS)
  (mem3 : word -> option byte) : Prop :=
  cb_doc C <> 0 -> ck_tree_ok ly3 S3 Lam3 W3 mem3 (cb_doc C) (cb_t C) (cb_D C).

(* what every boundary after the prologue carries *)
Definition crs_base_B (CTX0 : list (list Z)) (C : crsC_B) (fxk : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k sp2 : Z) : Prop :=
  crs_pre_B CTX0 C /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  crs_J_B C ly3 S3 Hp3 W3 mem3 md3 k /\
  crs_frame_B C ly3 S3 W3 mem3 /\ crs_saved_B C W3 mem3 /\ crs_slot_B C W3 mem3 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W3) mem3) /\
  YAkMemnorm.memnorm SEGS mem3 /\
  getr regs3 3 = getr (cb_regs C) 3 /\ getr regs3 4 = getr (cb_regs C) 4 /\
  spZ (cb_regs C) - CRS_FRAME_B <= sp2 /\ sp2 <= spZ (cb_regs C) - 128 /\ sp2 mod 32 = 0 /\
  crs_dpok_B C.
(* the same boundary over a world relation R: crs_base_B with crs_J_B replaced by crs_JR_B R, every other conjunct
   unchanged (crs_base_B_R_wle: equal at wle; crs_baseR_B_mono: a larger relation keeps it) *)
Definition crs_baseR_B (R : world SEGS -> world SEGS -> Prop) (CTX0 : list (list Z)) (C : crsC_B)
  (fxk : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) (k sp2 : Z) : Prop :=
  crs_pre_B CTX0 C /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  crs_JR_B R C ly3 S3 Hp3 W3 mem3 md3 k /\
  crs_frame_B C ly3 S3 W3 mem3 /\ crs_saved_B C W3 mem3 /\ crs_slot_B C W3 mem3 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W3) mem3) /\
  YAkMemnorm.memnorm SEGS mem3 /\
  getr regs3 3 = getr (cb_regs C) 3 /\ getr regs3 4 = getr (cb_regs C) 4 /\
  spZ (cb_regs C) - CRS_FRAME_B <= sp2 /\ sp2 <= spZ (cb_regs C) - 128 /\ sp2 mod 32 = 0 /\
  crs_dpok_B C.
Lemma crs_base_B_R_wle : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  crs_base_B CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 =
  crs_baseR_B (@wle SEGS) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2.
Proof. reflexivity. Qed.
Lemma crs_baseR_B_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  crs_baseR_B R1 CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_baseR_B R2 CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2.
Proof.
intros R1 R2 H12 CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 (HP & HZ & HK & HJ & HT).
exact (conj HP (conj HZ (conj HK (conj (crs_JR_B_mono R1 R2 H12 C ly3 S3 Hp3 W3 mem3 md3 k HJ) HT)))).
Qed.

(* ---- the register sets (the plan's roles, measured on the B' body) ---- *)
(* sp and s1 the realigned sp, s0 the entry sp, s2 and s10 the fake frame (s2 <> 0, so s10 = s2), s11 the shadow
   offset (`ld s11, 0(a1)` through the GOT word) *)
Definition crs_rbase_B (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) :=
  [(2%bv, sp2); (8%bv, spZ (cb_regs C)); (9%bv, sp2); (18%bv, cF_B C); (26%bv, cF_B C); (27%bv, SHADOW_OFF)].
(* s9, the frame's shadow (`srli s9, s10, 3`; `add s9, s9, s11`) *)
Definition crs_rsh_B (C : crsC_B) : list (bv 5 * Z) := [(25%bv, shadow_addr (cF_B C))].
(* s3 = doc, s4 = size, s5 = data (B' keeps both to the END: the compact pick is the fuzz_pick CALL, which takes
   them as its arguments and preserves them; A''s inlined third loop ate s4 and s5) *)
Definition crs_rargs_B (C : crsC_B) : list (bv 5 * Z) :=
  [(19%bv, cb_doc C); (20%bv, cSize_B C); (21%bv, cb_data C)].
(* s6 = fuzz_alloc_live () at entry *)
Definition crs_rlive_B (C : crsC_B) : list (bv 5 * Z) := [(22%bv, Ledger.lsum (cb_Lam C))].
(* s8 from W1's auipc on: the ran-out cell base *)
Definition crs_rro_B : list (bv 5 * Z) := [(24%bv, CRS_RO_B)].

(* ---- the counter arithmetic (image-free: the same as A') ---- *)
(* the starved reading's share of the growth *)
Definition crs_first_B (C : crsC_B) : Z :=
  if cb_took C =? 0 then 0 else ck_pick (cb_tb C) (cb_took C) + 1.
(* g_count after the starved reading (exact once check #1 passed), after the pretty pair, after the compact pair *)
Definition crs_cnt1_B (C : crsC_B) : Z := cb_cnt C + crs_first_B C.
Definition crs_cnt2_B (C : crsC_B) : Z := crs_cnt1_B C + cN1_B C + ck_pick (cb_tb C) (cN1_B C) + 1.
Definition crs_cnt3_B (C : crsC_B) : Z := crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C) + 1.
(* after the starved reading: nothing when took = 0, else one more than the injected failure's index at most *)
Definition crs_cnt_R_B (C : crsC_B) (cnt1 ran1 : Z) : Prop :=
  (cb_took C = 0 -> cnt1 = cb_cnt C) /\
  (cb_took C <> 0 -> cb_cnt C + 1 <= cnt1 <= cb_cnt C + ck_pick (cb_tb C) (cb_took C) + 1 /\
                     (ran1 = 0 -> cnt1 = cb_cnt C + ck_pick (cb_tb C) (cb_took C) + 1)).
(* a whole write of the tree, pretty (p = true) or compact: at least one call, all of them when nothing was
   refused *)
Definition crs_kfull_B (C : crsC_B) (p : bool) (kk ranp : Z) : Prop :=
  1 <= kk <= PjWriteHyp.wcalls (cb_t C) p /\ (ranp = 0 -> kk = PjWriteHyp.wcalls (cb_t C) p).
(* what R and F need of the count: crs_post_B's bound and growth *)
Definition crs_cnt_end_B (C : crsC_B) (cnt3 ran3 : Z) : Prop :=
  cnt3 <= cb_cnt C + ck_crcs_max (cb_tb C) (cb_took C) (cb_doc C) (cb_t C) /\
  (ran3 = 0 -> cnt3 = cb_cnt C + ck_crcs_growth (cb_tb C) (cb_took C) (cb_doc C) (cb_t C)).

(* ======================================================================================================== *)
(* ---- THE CONTINUATION PREDICATES, one per segment entry, from the last one backwards. Each is stated over
   (C, the state at its pc) and concludes crs_post_B C. Lane lemma shapes:
     R: crs_from_R_B          F: crs_from_R_B -> crs_from_F_B
     X3: crs_from_F_B -> crs_from_R_B -> crs_from_X3_B      H3: crs_from_X3_B -> crs_from_H3_B
     Z: crs_from_R_B -> crs_from_H3_B -> crs_from_Z_B       X2: crs_from_F_B -> crs_from_Z_B -> crs_from_X2_B
     H2: crs_from_R_B -> crs_from_X2_B -> crs_from_H2_B     W1: crs_from_R_B -> crs_from_H2_B -> crs_from_W1_B
     X1: crs_from_R_B -> crs_from_W1_B -> crs_from_X1_B
     H1: crs_from_X1_B -> crs_from_R_B -> crs_from_W1_B -> crs_from_H1_B
     E: (forall p, crs_from_H1_B (crs_with_fpos_B C p)) -> crs_from_E_B C ---- *)

(* R (+736): `sb -8` over the local's shadow bytes 4-10, the retired magic at F, then (s2 <> 0) `sb -11` over all
   sixteen shadow bytes and the flag release (the byte at the word at s2 + 120 set to 0) (aj_flag_store_x); the
   s2 = 0 arm (+864) is refuted by s2 = F <> 0; the restores from s0 - 128; ret. Reached by: X1's doc = 0 arm,
   X3's live == s6 arm (and H1's took = 0, doc = 0 arm). At the kit's cut the ran-out arms of W1 / H2 / Z and the entry
   from F are refuted (nothing is refused: crs_core_B's ran3 = cb_ran C = 0), so they never reach R. *)
(* THE RE-HIDING MOVE: every continuation below concludes at the text's relation, SRr' SEGS RZ_cf (a step valid
   under SRr is one under SRr' by YA0nH.SRr_SRr'); the cuts AFTER pj_parse (W1 .. R, F) carry the boundary at wle'
   (crs_baseR_B (wle' SEGS RZ_cf)), the cuts before it (E, H1, X1) at wle (crs_base_B). crs_post_B is unchanged. *)
Definition crs_from_R_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt3 ran3,
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 ran3 (crs_evs_at_R_B C) ->
  PRH_Base.bytes_at W3 mem3 (cb_data C) (cb_tb C) ->
  crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  crs_cnt_end_B C cnt3 ran3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_R_B) regs3 mem3 md3) (crs_post_B C).

(* F (+728): fuzz_free (s7), then R. Its ONLY entry is the RAN arm of checks #3 (X2) and #5 (X3), right after the
   injected pj_write, which needs ran3 = 1. At the kit's cut that arm is REFUTED (the writers' prh_granted keeps g_ran_out:
   PRW_CrsModel.crs_ran_of_granted; crs_core_B's ran3 = cb_ran C = 0), so crs_from_F_B is never entered; F's lemma
   is kept, proved, for the shape of the walk. Its statement: the writer post on its FAILED arm (w_failed <> 0),
   s7 = q = 0 and Lam / the blocks back (crs_perm_B); no position is asked, and the NULL free goes through the walk's
   position-free interim for fuzz_free (NULL). *)
Definition crs_from_F_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt3 ran3 q,
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ [(23%bv, q)]) ->
  crs_core_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 ran3 (crs_evs_at_F_B C) ->
  ran3 = 1 -> q = 0 -> crs_perm_B C ly3 S3 Lam3 ->
  PRH_Base.bytes_at W3 mem3 (cb_data C) (cb_tb C) ->
  crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  crs_cnt_end_B C cnt3 ran3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_F_B) regs3 mem3 md3) (crs_post_B C).

(* X3 (+1072, the fuzz_pick return site, crs_pc_X3_ret_B): a0 = ck_pick tb N0, the index the compact injected write
   must fail at (B' reads it from the CALL; A' computes it inline, so its X3 carries the count and the hash and
   refutes a count == s7 arm that B' does not have). fail (a0); pj_write (doc, 0) -> s7 (NULL: the injected failure
   is reached); fail (-1); check #5: OWN arm -> F (refuted: own = 0, header), RAN arm -> F; `bnez s7` -> ABORT
   refuted (s7 = 0); fuzz_alloc_live == s6 -> R (crs_lsum_perm_B), else ABORT refuted. *)
Definition crs_from_X3_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  cb_doc C <> 0 ->
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ [(19%bv, cb_doc C)] ++ crs_rlive_B C ++ crs_rro_B
                      ++ [(23%bv, crs_cnt2_B C); (10%bv, cPick0_B C)]) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt2_B C + cN0_B C) 0 (crs_evs_at_X3_B C) ->
  PRH_Base.bytes_at W3 mem3 (cb_data C) (cb_tb C) ->
  crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_X3_B) regs3 mem3 md3) (crs_post_B C).

(* H3 (+1052): count (a0), `sub a2, a0, s7` (= N0), `mv a0, s5` / `mv a1, s4`, then the CALL `jal fuzz_pick` at
   +1068 (the kit's tfuzz_pick_specX: a leaf that allocates nothing, keeps the ledger and the bytes and returns
   ck_pick tb N0; its own report arm and its UBSan trap are its text's, not this walk's). Its three premises on the
   input are crs_src_rd_at_B, and its `0 <= n < 2 ^ 64` is crs_N0_rng_B. s7 = the count before the whole compact
   write; check #4 passed, so that write made all N0 calls. *)
Definition crs_from_H3_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  cb_doc C <> 0 ->
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B
                      ++ [(23%bv, crs_cnt2_B C)]) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt2_B C + cN0_B C) 0 (crs_evs_at_H3_B C) ->
  crs_dat_B C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_H3_B) regs3 mem3 md3) (crs_post_B C).

(* Z (+992): s7 = 0 (the injected pretty write's NULL) so `bnez s7` -> ABORT is refuted; fuzz_alloc_live == s6
   (crs_lsum_perm_B) so `bne` -> ABORT is refuted; count -> s7; pj_write (doc, 0); fuzz_free; count; count == before
   (+1032) refuted (crs_kfull_B); check #4: OWN arm -> R (refuted: own = 0, header), RAN arm -> R; else H3. *)
Definition crs_from_Z_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  cb_doc C <> 0 ->
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B
                      ++ [(23%bv, 0)]) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt2_B C) 0 (crs_evs_at_Z_B C) ->
  crs_dat_B C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_Z_B) regs3 mem3 md3) (crs_post_B C).

(* X2 (+664): a0 = the count after the whole pretty write, s7 = the count before it, a2 = the hash of L2; fail
   (h % N1) (the a0 = s7 arm refuted); pj_write (doc, 1) -> s7; fail (-1); check #3: OWN arm -> F (refuted: own = 0,
   header), RAN arm -> F (ran = 1, s7 = 0), else Z (s7 = 0, g_ran_out = 0, the injected write made pick + 1 calls). *)
Definition crs_from_X2_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  cb_doc C <> 0 ->
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B
                      ++ [(23%bv, crs_cnt1_B C); (10%bv, crs_cnt1_B C + cN1_B C); (12%bv, cHash_B C)]) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt1_B C + cN1_B C) 0 (crs_evs_at_X2_B C) ->
  crs_dat_B C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_X2_B) regs3 mem3 md3) (crs_post_B C).

(* H2 (+528): check #2 (its lbu is H2's first instruction): OWN arm -> R (refuted: own = 0, header), RAN arm -> R;
   count (a0); the second djb2 loop L2 (copies of s4 / s5, a0 kept), its three UBSan arms (+576 / +588 / +592) and
   its report arm (+660) refuted. s7 = the count before the whole pretty write (exact: check #1 passed), which made
   k1 calls. *)
Definition crs_from_H2_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 ran3 k1,
  cb_doc C <> 0 ->
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B
                      ++ [(23%bv, crs_cnt1_B C)]) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt1_B C + k1) ran3 (crs_evs_at_H2_B C) ->
  crs_dat_B C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  crs_kfull_B C true k1 ran3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_H2_B) regs3 mem3 md3) (crs_post_B C).

(* W1 (+476): auipc s8 (= CRS_RO_B, crs_ro_atoms_B); check #1: OWN arm -> R (refuted: own = 0, header), RAN arm
   (refuted at the kit's cut: ran1 = cb_ran C = 0); count -> s7; pj_write (doc, 1); fuzz_free (its text); count; count ==
   before (+524) refuted (crs_kfull_B). The reading's count and flag are cnt1 / ran1. *)
Definition crs_from_W1_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt1 ran1,
  cb_doc C <> 0 ->
  crs_baseR_B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt1 ran1 (crs_evs_at_W1_B C) ->
  crs_dat_B C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  crs_cnt_R_B C cnt1 ran1 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_W1_B) regs3 mem3 md3) (crs_post_B C).

(* X1 (+416): s8 = F + 32 (the local), fuzz_alloc_fail (h % took) (a1 = the hash of L1, s7 = took <> 0), pj_parse
   (data, size, s8) (refused: the injected failure is inside its calls), fuzz_alloc_fail (-1), check_reject_clean
   (rc, s8, s6) (premise: the kit's tcheck_reject_clean_specX at B'), then beqz doc (+472): doc = 0 -> R, else W1. Entered
   with no budget spent (cb_ws C = []): pj_parse's room comes from the text's, and its cursor traces are the walk's
   only wild ones; X1 continues at the REBASED context (crs_with_dp_B). *)
Definition crs_from_X1_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  cb_took C <> 0 -> cb_ws C = [] ->
  crs_base_B CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C
                      ++ [(23%bv, cb_took C); (11%bv, cHash_B C)]) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 (cb_Lam C) (cb_peak C) (cb_cnt C) (cb_ran C) (crs_evs_at_X1_B C) ->
  crs_dat_B C ly3 S3 Hp3 W3 mem3 (cb_Lam C) -> crs_tree_B C ly3 S3 (cb_Lam C) W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_X1_B) regs3 mem3 md3) (crs_post_B C).

(* H1 (+296): a0 = fuzz_alloc_live () (= lsum Lam), `mv s6, a0`; beqz took: took = 0 -> X1's beqz doc at +472
   (run here; doc = 0 -> R, else W1 with cnt1 = cb_cnt, ran1 = cb_ran); a1 = 5381; beqz size -> X1; else the first
   djb2 loop L1 (+332 .. +396), its three UBSan arms (+332 / +344 / +348) and its report arm (+412) refuted; exit X1
   with a1 = cHash_B. *)
Definition crs_from_H1_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  cb_ws C = [] ->
  crs_base_B CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C
                      ++ [(23%bv, cb_took C); (10%bv, Ledger.lsum (cb_Lam C))]) ->
  crs_live_B C ly3 S3 Hp3 W3 mem3 (cb_Lam C) (cb_peak C) (cb_cnt C) (cb_ran C) (crs_evs_at_H1_B C) ->
  crs_dat_B C ly3 S3 Hp3 W3 mem3 (cb_Lam C) -> crs_tree_B C ly3 S3 (cb_Lam C) W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg_B fxk (BASE + CRS_PC_H1_B) regs3 mem3 md3) (crs_post_B C).

(* E (+0, the entry, the text's own configuration): the prologue (13 saves, `addi s0, sp, 128`, `andi sp, sp, -32`),
   the use-after-return word (alx_const: 1, so the call is made), __asan_stack_malloc_1 (128) at +120
   (aj_stack_malloc_at_x with crs_cap_B; the real-stack fallback +144 .. +168 is refuted: the returned frame is not
   0, alx_frames' in_app), `sd s10, 16(s1)`, the frame header (magic 0x41b58ab3, descriptor, pc), s9, the sixteen
   shadow pokes, fuzz_alloc_live; exit H1. *)
Definition crs_from_E_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  crs_pre_B CTX0 C ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (cb_W C) (cfg_at SEGS (SIGMA AS_check_reject_clean_starved) (cb_regs C) (cb_mem C) (cb_md C))
    (crs_post_B C).

(* ======================================================================================================== *)
(* ---- THE TRANSPORT FACTS the segments share (the A' kit's CrsKeep at B': the reader's home, the ledger, the
   tree's visibility, the entry's fake frames and the doc's object home). Derivable from AR_laws_x and ajournal_x's
   own clauses; proved once, passed to every lane. No field for g_own_ran_out or g_most (header). ---- *)
Record CrsKeep_B : Prop := {
  (* the shadow of a window the reader's home premise names, at any ARx state whose ledger lists Lam *)
  kpb_home_sh : forall ly S Hp W mem md Lam peak cnt fail ran most own p n,
    ARx ly S Hp W mem md ->
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    PRH_FnReader.prhReader_home B ly S Hp Lam p n ->
    0 < n -> 0 <= p -> p + n <= YM05.alloc_ceiling ->
    range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\
    shadow_hull_vis (aview SEGS (w_H W) mem) p n;
  (* the home moves with the ledger: a permutation of Lam and of the allocator blocks keeps it *)
  kpb_home_move : forall ly S Hp W mem Lam peak cnt fail ran most own ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3
      most3 own3 p n,
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 ->
    Permutation Lam3 Lam -> Permutation (ablocks B ly3 S3) (ablocks B ly S) ->
    PRH_FnReader.prhReader_home B ly S Hp Lam p n -> PRH_FnReader.prhReader_home B ly3 S3 Hp3 Lam3 p n;
  (* the shadow of a tree's blocks, which pj_write asks of a tree it is handed *)
  kpb_tree_vis : forall ly S Hp W mem md Lam peak cnt fail ran most own D,
    ARx ly S Hp W mem md ->
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    (forall bk, In bk D -> In bk Lam) -> PRH_FnWriter.prhWriter_tree_vis W mem D;
  (* a fake frame of the ENTRY state keeps its bytes and its shadow bytes across the whole journal (FP = []) *)
  kpb_frame_keep : forall STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a,
    AJ STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    In (cid, pos) (frames S) ->
    (in_zr a (frame_rng ly (cid, pos)) \/
     in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a;
  (* so a 56-byte object inside such a frame keeps its home, its addressability and its hull *)
  kpb_obj_keep : forall STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p,
    ARx ly S Hp W mem md ->
    AJ STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p
}.

(* ======================================================================================================== *)
(* ---- KIT LEMMAS ---- *)

(* moving a state's depot to its own depot changes nothing (the journal's entry before any rebase) *)
Lemma crs_set_depot_id_B : forall S, YG00.set_depot (st_depot S) S = S.
Proof. intros S. destruct S. reflexivity. Qed.

(* a later layout of the journal keeps the frame's address and its flag address (alx_layout) *)
Lemma crs_ly_keep_B : forall ly S Hp W mem md ly' cid pos,
  ARx ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
intros ly S Hp W mem md ly' cid pos HAR Hle.
pose proof LAWS as HLY. apply alx_layout in HLY.
destruct (HLY ly S Hp W mem md ly' HAR Hle) as (_ & Hfa & _).
split; [apply Hfa|].
pose proof (Hfa cid pos) as E. unfold frame_addr in E. unfold flag_addr. lia.
Qed.

(* at a boundary: the frame register value cF_B C is the frame at the current layout too *)
Lemma crs_cF_keep_B : forall CTX0 C ly3 S3 Hp3 W3 mem3 md3 k,
  crs_pre_B CTX0 C -> crs_J_B C ly3 S3 Hp3 W3 mem3 md3 k ->
  frame_addr ly3 CRS_CID_B (cb_fpos C) = cF_B C /\
  flag_addr ly3 CRS_CID_B (cb_fpos C) = flag_addr (cb_ly C) CRS_CID_B (cb_fpos C).
Proof.
intros CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ.
destruct HP as (HF & _). destruct HF as ((HAR & _) & _).
unfold crs_J_B in HJ. destruct HJ as (_ & Hle & _).
exact (crs_ly_keep_B _ _ _ _ _ _ ly3 CRS_CID_B (cb_fpos C) HAR Hle).
Qed.
(* the same over a world relation R (it reads only the journal's layout conjunct) *)
Lemma crs_cF_keepR_B : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k,
  crs_pre_B CTX0 C -> crs_JR_B R C ly3 S3 Hp3 W3 mem3 md3 k ->
  frame_addr ly3 CRS_CID_B (cb_fpos C) = cF_B C /\
  flag_addr ly3 CRS_CID_B (cb_fpos C) = flag_addr (cb_ly C) CRS_CID_B (cb_fpos C).
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ.
destruct HP as (HF & _). destruct HF as ((HAR & _) & _).
unfold crs_JR_B, ajournal_xR, ajournal_xwR, ajournal_xbR in HJ. destruct HJ as (_ & Hle & _).
exact (crs_ly_keep_B _ _ _ _ _ _ ly3 CRS_CID_B (cb_fpos C) HAR Hle).
Qed.

(* THE TWO JOURNAL FACTS AT A MOVED ENTRY DEPOT (crs_J_B's form): no clause they read looks at the entry depot, so
   CrsKeep_B's kpb_frame_keep / kpb_obj_keep hold of a journal from `set_depot d S` with ARx at S; proved here as
   CrsTopBp.v proves the record's fields *)
Lemma crs_frame_keep_dp_B : forall STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a,
  AJ STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a.
Proof.
intros STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a HJ Hin Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
exact (HF cid pos a Hin Ha (inFP_nil a)).
Qed.
Lemma crs_obj_keep_dp_B : forall STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p,
  ARx ly S Hp W mem md ->
  AJ STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p.
Proof.
intros STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p HAR HJ HO.
unfold ck_obj_home, ck_in_frame in HO |- *.
destruct HO as (Hp8 & (cid & pos & Hin & Hlo & Hhi) & HRA).
pose proof HJ as (_ & Hle & _ & _ & _ & Hfr & _).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md ly3 HAR Hle) as (_ & Hfa & _).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (F32 & _ & _ & _).
split; [exact Hp8|]. split.
- exists cid, pos. split; [rewrite Hfr; apply in_or_app; right; exact Hin|].
  rewrite (Hfa cid pos). split; lia.
- intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  apply (crs_frame_keep_dp_B STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos _ HJ Hin).
  right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
Qed.

(* THE TWO JOURNAL FACTS OVER A WORLD RELATION R, at a moved entry depot: neither reads the world conjunct, so they
   hold of every R (the R forms the segments use after a free or a realloc) *)
Lemma crs_frame_keep_dpR_B : forall (R : world SEGS -> world SEGS -> Prop) STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3
  W3 mem3 md3 k cid pos a,
  ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a.
Proof.
intros R STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a HJ Hin Ha.
unfold ajournal_xR, ajournal_xwR, ajournal_xbR in HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
exact (HF cid pos a Hin Ha (inFP_nil a)).
Qed.
Lemma crs_obj_keep_dpR_B : forall (R : world SEGS -> world SEGS -> Prop) STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3
  W3 mem3 md3 k p,
  ARx ly S Hp W mem md ->
  ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p.
Proof.
intros R STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p HAR HJ HO.
unfold ck_obj_home, ck_in_frame in HO |- *.
destruct HO as (Hp8 & (cid & pos & Hin & Hlo & Hhi) & HRA).
pose proof HJ as HJ0. unfold ajournal_xR, ajournal_xwR, ajournal_xbR in HJ0.
destruct HJ0 as (_ & Hle & _ & _ & _ & Hfr & _).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md ly3 HAR Hle) as (_ & Hfa & _).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (F32 & _ & _ & _).
split; [exact Hp8|]. split.
- exists cid, pos. split; [rewrite Hfr; apply in_or_app; right; exact Hin|].
  rewrite (Hfa cid pos). split; lia.
- intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  apply (crs_frame_keep_dpR_B R STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos _ HJ Hin).
  right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
Qed.
(* the R forms for a journal from an UNDISTURBED entry state (a callee's journal): the moved-depot forms at d :=
   st_depot S, since set_depot (st_depot S) S = S (crs_set_depot_id_B) *)
Lemma crs_frame_keepR_B : forall (R : world SEGS -> world SEGS -> Prop) STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3
  W3 mem3 md3 k cid pos a,
  ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a.
Proof.
intros R STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a HJ.
rewrite <- (crs_set_depot_id_B S) in HJ.
exact (crs_frame_keep_dpR_B R STK0 sp0 ly S (st_depot S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a HJ).
Qed.
Lemma crs_obj_keepR_B : forall (R : world SEGS -> world SEGS -> Prop) STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3
  W3 mem3 md3 k p,
  ARx ly S Hp W mem md ->
  ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p.
Proof.
intros R STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p HAR HJ.
rewrite <- (crs_set_depot_id_B S) in HJ.
exact (crs_obj_keep_dpR_B R STK0 sp0 ly S (st_depot S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p HAR HJ).
Qed.

(* the E lane's capacity fact at the entry state *)
Lemma crs_cap_pre_B : forall CTX0 C, crs_pre_B CTX0 C -> count_cid 1 (frames (cb_S C)) < fs_frames 1.
Proof.
intros CTX0 C H. apply crs_cap_B.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hfr & _).
exact Hfr.
Qed.

(* THE INPUT WINDOW AT A BOUNDARY (B' only): the fuzz_pick CALL of H3 asks src_rd of the data at the state it is
   made in. crs_dat_B holds the four state-dependent conjuncts; the other three (the floor, the ceiling and the
   range) are state-free and come from the text's own entry premise. *)
Lemma crs_src_rd_at_B : forall CTX0 C ly3 S3 Hp3 W3 mem3 Lam3,
  crs_pre_B CTX0 C -> crs_dat_B C ly3 S3 Hp3 W3 mem3 Lam3 ->
  src_rd W3 mem3 (cb_data C) (cb_tb C).
Proof.
intros CTX0 C ly3 S3 Hp3 W3 mem3 Lam3 HP HD.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
destruct Hsrc as (_ & Hfloor & Hceil & Hrng & _).
destruct HD as (Hb & _ & Hra & Hhull).
unfold src_rd. unfold cSize_B in Hra, Hhull.
split; [exact Hb|]. split; [exact Hfloor|]. split; [exact Hceil|]. split; [exact Hrng|].
split; [exact Hra|exact Hhull].
Qed.

(* the compact write's call count is a machine word: fuzz_pick's `0 <= n < 2 ^ 64` at n = N0 (B' only) *)
Lemma crs_N0_rng_B : forall CTX0 C, crs_pre_B CTX0 C -> cb_doc C <> 0 -> 0 <= cN0_B C < 2 ^ 64.
Proof.
intros CTX0 C HP Hd.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htree & _).
destruct Htree as [H0 | (_ & _ & Hw0 & _)]; [contradiction|].
assert (Hle : PjWriteHyp.wlen (cb_t C) false + 1 <= 2 ^ 62).
{ assert (E : 2 ^ 24 <= 2 ^ 62) by (vm_compute; discriminate). lia. }
pose proof (crs_wN_le (cb_t C) false Hle) as Hub.
assert (Hlb : 0 <= cN0_B C) by (unfold cN0_B, PjWriteHyp.wcalls; apply Nat2Z.is_nonneg).
assert (Hwl : 0 <= PjWriteHyp.wlen (cb_t C) false)
  by (unfold PjWriteHyp.wlen; apply Nat2Z.is_nonneg).
assert (E64 : 2 ^ 24 <= 2 ^ 64) by (vm_compute; discriminate).
unfold cN0_B, PjWriteHyp.wcalls in *. lia.
Qed.

(* the growth at the two ends: the doc = 0 exit after the reading, the normal end after the compact pair *)
Lemma crs_growth_doc0_B : forall C, cb_doc C = 0 ->
  cb_cnt C + ck_crcs_growth (cb_tb C) (cb_took C) (cb_doc C) (cb_t C) = crs_cnt1_B C.
Proof.
intros C H. unfold ck_crcs_growth, crs_cnt1_B, crs_first_B.
assert (E : (cb_doc C =? 0) = true) by (apply Z.eqb_eq; exact H).
rewrite E. cbv beta iota. lia.
Qed.
Lemma crs_growth_doc_B : forall C, cb_doc C <> 0 ->
  cb_cnt C + ck_crcs_growth (cb_tb C) (cb_took C) (cb_doc C) (cb_t C) = crs_cnt3_B C.
Proof.
intros C H. unfold ck_crcs_growth, crs_cnt3_B, crs_cnt2_B, crs_cnt1_B, crs_first_B, cN1_B, cN0_B.
assert (E : (cb_doc C =? 0) = false) by (apply Z.eqb_neq; exact H).
rewrite E. cbv beta iota. lia.
Qed.

(* ---- THE RUN EVENTS: the entry premise, its split at the boundaries, and the free sites' events ---- *)

(* the entry premise of the text, as crs_pre_B carries it *)
Lemma crs_run_of_pre_B : forall CTX0 C, crs_pre_B CTX0 C ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (crs_evs_B C).
Proof.
intros CTX0 C H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _).
exact Hr.
Qed.

(* the model's write makes at least one allocation (PRW_CrsModel.crs_wN_pos at PresetReqAt's wcaps) *)
Lemma crs_wcalls_pos_B : forall t p, (1 <= PresetReqAt.wcalls t p)%nat.
Proof. intros t p. unfold PresetReqAt.wcalls, PresetReqAt.wcaps. exact (crs_wN_pos t p). Qed.

Lemma crs_sw_S_B : forall x t p rest, PresetReqAt.starved_write x t p rest =
  PresetReqAt.w_evs t p ++ PresetReqAt.w_free t p ++
  PresetReqAt.w_starved t p (PresetReqAt.pick x (PresetReqAt.wcalls t p)) ++ rest.
Proof.
intros x t p rest. pose proof (crs_wcalls_pos_B t p) as H. unfold PresetReqAt.starved_write.
destruct (PresetReqAt.wcalls t p) as [|n] eqn:E; [lia | reflexivity].
Qed.

(* the whole list at the two ends: doc = 0 ends after the reading (W1's prefix), a tree after the compact
   injected write (X3's prefix and that write's events) *)
Lemma crs_evs_doc0_B : forall C, cb_doc C = 0 -> crs_evs_B C = crs_evs_at_W1_B C.
Proof.
intros C H. unfold crs_evs_B, ck_crcs_evs, crs_evs_at_W1_B, crs_ev_sp_B.
rewrite (proj2 (Z.eqb_eq (cb_doc C) 0) H). cbv iota. rewrite app_nil_r. reflexivity.
Qed.
Lemma crs_evs_doc_B : forall C, cb_doc C <> 0 -> crs_evs_B C = crs_evs_at_X3_B C ++ crs_ev_ws_B C false.
Proof.
intros C H. unfold crs_evs_B, ck_crcs_evs.
rewrite (proj2 (Z.eqb_neq (cb_doc C) 0) H). cbv iota.
unfold PresetReqAt.starved_writes. rewrite !crs_sw_S_B, app_nil_r.
unfold crs_evs_at_X3_B, crs_evs_at_H3_B, crs_evs_at_Z_B, crs_evs_at_X2_B, crs_evs_at_H2_B, crs_evs_at_W1_B,
  crs_ev_sp_B, crs_ev_w_B, crs_ev_wf_B, crs_ev_ws_B.
repeat rewrite <- app_assoc. reflexivity.
Qed.

(* a split of the list gives the second part at the position after the first (PRH_Base.prh_run_at_app_iff) *)
Lemma crs_run_split_B : forall C e1 e2, crs_evs_B C = e1 ++ e2 ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (crs_evs_B C) ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) e1 /\
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length e1)%nat e2.
Proof.
intros C e1 e2 E H. rewrite E in H. exact (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H).
Qed.

(* the three room premises crs_pre_B appends at the cut (wild room, the two room counts), for the pj_parse call *)
Lemma crs_pre_room_B : forall CTX0 C, crs_pre_B CTX0 C ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_reject_clean_starved) (st_depot (cb_S C)) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (cb_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (cb_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros CTX0 C H. unfold crs_pre_B in H.
repeat match type of H with
| YCbqGwild.wild_room _ _ _ _ /\ _ => destruct H as (H1 & H2 & H3 & _); exact (conj H1 (conj H2 H3))
| _ /\ _ => destruct H as [_ H]
end.
Qed.

(* THE RUN HAS AT MOST 4 CALLS: crs_pre_B's conjunct, the premise a callee's text takes for its hull budget paid
   from the run's position (the writer text's `length rp_os <= 4`) *)
Lemma crs_pre_los_B : forall CTX0 C, crs_pre_B CTX0 C -> (length (cb_rp_os C) <= 4)%nat.
Proof.
intros CTX0 C HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & HL & _).
exact HL.
Qed.

(* THE CONSUMER WINDOW of a callee (the text's prh_cons_from, crs_pre_B's last conjunct): a split of the run's events
   gives the middle part's window (PRH_Base.prh_cons_from_sub), which a callee's text takes at its own call *)
Lemma crs_cons_split_B : forall CTX0 C e1 e2 e3, crs_evs_B C = e1 ++ e2 ++ e3 -> crs_pre_B CTX0 C ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length e1)%nat (length e2).
Proof.
intros CTX0 C e1 e2 e3 E H. unfold crs_pre_B in H.
repeat match type of H with _ /\ _ => destruct H as [_ H] end.
rewrite E in H. apply (PRH_Base.prh_cons_from_sub _ _ _ _ (length (e1 ++ e2 ++ e3)) (length e1) (length e2)); [|exact H].
rewrite !app_length. lia.
Qed.

(* THE FREE SITES' EVENTS: with a tree, the run's event at W1's fuzz_free (the whole pretty text, +516) and at Z's
   fuzz_free (the whole compact text, +1024) is the HFr of that text's last capacity plus the head, at the EXACT
   position the boundary's prefix and the write's w_evs name. tfuzz_free_specX's p <> 0 arm takes it as its
   nth_error premise (n + cf_head = that request). F's fuzz_free (s7) needs none: s7 = NULL when nothing was
   refused (crs_from_F_B). *)
Lemma crs_room_evs_of_run_B : forall C, cb_doc C <> 0 ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (crs_evs_B C) ->
  nth_error (PresetRun.hruns ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C))
    (cb_rp_i C + length (crs_evs_at_W1_B C ++ crs_ev_w_B C true))%nat =
    Some (PresetReqAt.HFr (last (PresetReqAt.wcaps (cb_t C) true) 0 + PresetReqAt.HEAD)) /\
  nth_error (PresetRun.hruns ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C))
    (cb_rp_i C + length (crs_evs_at_Z_B C ++ crs_ev_w_B C false))%nat =
    Some (PresetReqAt.HFr (last (PresetReqAt.wcaps (cb_t C) false) 0 + PresetReqAt.HEAD)).
Proof.
intros C Hd H. pose proof (crs_evs_doc_B C Hd) as E. split.
- assert (E1 : crs_evs_B C = (crs_evs_at_W1_B C ++ crs_ev_w_B C true) ++ crs_ev_wf_B C true ++
                 (crs_ev_ws_B C true ++ crs_ev_w_B C false ++ crs_ev_wf_B C false ++ crs_ev_ws_B C false)).
  { rewrite E. unfold crs_evs_at_X3_B, crs_evs_at_H3_B, crs_evs_at_Z_B, crs_evs_at_X2_B, crs_evs_at_H2_B.
    repeat rewrite <- app_assoc. reflexivity. }
  destruct (crs_run_split_B C _ _ E1 H) as [_ H2].
  apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H2 as [H3 _].
  exact (proj1 (prh_run_at_one _ _ _ _
    (PresetReqAt.HFr (last (PresetReqAt.wcaps (cb_t C) true) 0 + PresetReqAt.HEAD))) H3).
- assert (E2 : crs_evs_B C = (crs_evs_at_Z_B C ++ crs_ev_w_B C false) ++ crs_ev_wf_B C false ++
                 crs_ev_ws_B C false).
  { rewrite E. unfold crs_evs_at_X3_B, crs_evs_at_H3_B. repeat rewrite <- app_assoc. reflexivity. }
  destruct (crs_run_split_B C _ _ E2 H) as [_ H2].
  apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H2 as [H3 _].
  exact (proj1 (prh_run_at_one _ _ _ _
    (PresetReqAt.HFr (last (PresetReqAt.wcaps (cb_t C) false) 0 + PresetReqAt.HEAD))) H3).
Qed.

(* ---- THE WRITER'S EXACT ADVANCE, by citation (the A' kit v4 lemmas at B'): tpj_write_specX (PRH_FnWriter.v at the
   cut) states prh_granted itself (DEAD-PJWRITE, under its prh_cons_from); PRH_Supply.v's
   prhWriter_pjw_evs_granted, prhWriter_pjw_evs_w_evs and prhWriter_pjw_evs_w_starved then name the events as the
   model's w_evs / w_starved, whose counts and pick are PjWriteHyp's and ck_pick's by the two bridges below.
   Image-free, as on A'. ---- *)

Lemma crs_wcalls_bridge_B : forall t p, PjWriteHyp.wcalls t p = Z.of_nat (PresetReqAt.wcalls t p).
Proof. intros t p. reflexivity. Qed.

Lemma crs_djb2_pick_h_B : forall x h, ck_djb2 h x = fold_left (fun h b => (h * 33 + b) mod 2 ^ 64) x h.
Proof.
intros x. induction x as [|c r IH]; intros h; cbn [ck_djb2 fold_left]; [reflexivity|].
rewrite IH. replace (33 * h) with (h * 33) by lia. reflexivity.
Qed.

Lemma crs_pick_bridge_B : forall x n, (0 < n)%nat -> ck_pick x (Z.of_nat n) = Z.of_nat (PresetReqAt.pick x n).
Proof.
intros x n Hn. destruct n as [|n']; [lia|].
unfold ck_pick, PresetReqAt.pick.
rewrite (proj2 (Z.eqb_neq (Z.of_nat (S n')) 0) ltac:(lia)). cbv iota.
unfold PresetReqAt.pick_h. rewrite <- crs_djb2_pick_h_B.
rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.

(* THE CHECK THAT crs_pre_B / crs_post_B ARE THE TEXT: an entry proof of crs_post_B for every C gives the kit's text at
   the B' instance (the journal's entry depot is the entry's own, no budget spent) *)
Lemma crs_spec_B : forall CTX0,
  (forall C, crs_pre_B CTX0 C ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (cb_W C)
       (cfg_at SEGS (SIGMA AS_check_reject_clean_starved) (cb_regs C) (cb_mem C) (cb_md C)) (crs_post_B C)) ->
  tcheck_reject_clean_starved_specX (fx := fx) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK CTX0.
Proof.
intros CTX0 HC. unfold tcheck_reject_clean_starved_specX.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most.
cbv zeta.
intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29
  P30 P31 P32.
pose proof (HC (mkCrsC_B ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most
                  rp_x rp_os rp_i rp_H0 rp_hist 0 (st_depot S) [])) as HS.
assert (Hpre : crs_pre_B CTX0 (mkCrsC_B ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most
                  rp_x rp_os rp_i rp_H0 rp_hist 0 (st_depot S) [])).
{ unfold crs_pre_B, cSize_B, crs_evs_B. repeat (split; [assumption|]). assumption. }
exact (HS Hpre).
Qed.

End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 671 of its 740 lines of code are new or changed and 859 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): the KIT of the walk of check_reject_clean_starved against the text
   tcheck_reject_clean_starved_specX. This file STATES the walk: the stage record, the text's pre and post, the
   boundary pcs, the stage invariants, the register sets and one continuation predicate per segment entry. The
   segment files (CrsSeg_<SEG>.v) prove the segments; the composition composes them backwards from R.
   rule 24: proves function check_reject_clean_starved (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an
   internal record of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search
   origin/ossv/recipes had no lib/A or lib/B, its released rows were lib/Prog (plain) and
   lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). Written new.
   INPUTS.
   - Pin A' asan sha256 1be0f53d96cb9d6c (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/A/Listing_prog.v blob 7ed1529926bd + lib/A/PAImg_prog.v blob 505a51ff7d08 (h-verbs-1 listings v3,
     cold/h-verbs-1-listing-pins102 74dcda1eda12: the d42e123915ae contents with a pre-evaluated slot tree). Entry
     0x82160 = slot 736 (A_entry_check_reject_clean_starved), 294 slots (736..1029).
   - The text: tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v:1756-1858,
     with lib/A/PRH_Base.v (prh_ledger with g_most and
     g_own_ran_out as its last two arguments, prh_run_at, prh_cons_from, prh_oks over the run's requests ns and most;
     fpre carries frm_zero (fp_csr fx)).
   THE BATCH KIT (the cut): DW is gone (crs_pre CTX0 C and every crs_from_<SEG> CTX0 C; prh_univ_closure B CTX0); the run's
   strtod model is keyed to ReaderRes.jr_strtod (the stage record has no rp_sm field); crs_pre appends the cut's wild
   room, the reading's two room counts and the consumer window prh_cons_from (crs_pre_k1, crs_cons_sub); crs_Q adds
   the cut's `ran' = ran`; crs_core states g_ran_out EXACTLY (ran3 = c_ran C): no allocation of the body is refused
   (pj_write's post states prh_granted, DEAD-PJWRITE; the starved reading's is tpj_parse_specX's own guarded conjunct
   THE OUTCOME OF AN INJECTED READING, lib/A/PRH_FnPj.v:736-754), so every ran-out check's RAN arm is refuted and
   crs_from_F (entered only with ran3 = 1) is vacuous.
   KIT CWPJ (the repaired prh_cw_pj, lib/A/PRH_Base.v:1779-1785): the cursor set names parse_items' free trace at the
   cursor end t0 + len and parse_string's at the slot word, both DATA words, so pj_parse's cursor traces are WILD on
   A' too (the old CW of fixed code-word traces no longer meets the text). The kit takes the B' budget route
   (CrsKitBp.v, a Theorem Labs lane): the record's c_dp / c_ws, the journal crs_J at the EMPTY budget from the entry with its
   depot moved to c_dp, crs_dpok in crs_base, crs_with_dp (X1 rebases after pj_parse), and crs_post is the text's
   budgeted post fpostFbm (wbudget [] (prh_wk F_check_reject_clean_starved)) itself (R unbases into it).
   KIT v3 (the E sweep): the entry ledger is `prh_ledger .. SIZE_MAXZ ran most 0` and the post's is `.. ran' most 0`;
   the separate prh_own / prh_most premises and post conjuncts are gone, folded into the ledger. Every boundary's
   ledger (crs_core) is `.. ran3 (c_most C) 0`: NO boundary has g_own_ran_out <> 0 (the function makes no harness-own
   allocation, and every callee's text keeps the ledger's own cell). The segments prove crs_post directly.
   KIT v2 (kept): the entry premise prh_run_at .. rp_i (ck_crcs_evs ..) is in crs_pre; the post's position is EXACT
   under ran' = 0; every boundary's position is exact too: crs_pos C evs ran3 S3 says `ran3 = 0 -> iface_room_pos ..
   (c_rp_i C + length evs) ..`, with evs the boundary's consumed prefix of ck_crcs_evs, crs_evs_at_<SEG>. After a
   REFUSAL (ran3 = 1) no position of the model's run describes the state (the text's own note), so none is stated.
   TEMPLATE (design only, never Required): the old-pin kit lib/A/Prog/CrsKitA.v at cold/h-w6u-rep-crs2 f83099b5b0d
   (A 0x820b0, 271 insns, the old text). Its shape is kept (Sections d / f over B, ARx, LAWS; the stage record; crs_pre
   / crs_post; crs_cfg / crs_regsat; the saved-slot, frame, slot, live, data and tree invariants; crs_from_<SEG>;
   CrsKeep). Every pc, register list and invariant below is re-derived for the A' body and the new text.
   THE CUT (the internal file SEGMENT-PLAN-Aprime.md, binding). Offsets from the entry, each 4 * a slot of the
   listing (crs_slots / crs_listing_cut check them against the listing):
     E    +0     prologue, the use-after-return word, __asan_stack_malloc_1 (+120), frame header, shadow pokes,
                 fuzz_alloc_live
     H1   +296   `mv s6, a0`; beqz took; the djb2 loop L1 (+328 .. +372) with its per-byte ASan check
     X1   +392   s8 = the local; fuzz_alloc_fail (h % took); pj_parse; fuzz_alloc_fail (-1); check_reject_clean;
                 beqz doc (+448) -> R
     W1   +452   own check #1 (+456 / +460), fuzz_alloc_ran_out; count; pj_write (doc, 1); fuzz_free; count;
                 count == before (+500) -> R
     H2   +504   own check #2 (+504 / +508), fuzz_alloc_ran_out; count; the djb2 loop L2
     X2   +616   fail (h % (count - k)); pj_write (doc, 1); fail (-1); own check #3 (+664 / +668), ran_out -> F,
                 else -> Z
     F    +680   fuzz_free (s7)
     R    +688   frame retire, the fake frame's release, restores, ret
     Z    +944   bnez s7 -> ABORT; live != s6 -> ABORT; count; pj_write (doc, 0); fuzz_free; count; count == before
                 (+984) -> R; own check #4 (+988 / +992), ran_out -> R
     H3   +1004  count; the djb2 loop L3 (it EATS s4 and s5)
     X3   +1092  fail (h % (count - k)); pj_write (doc, 0); fail (-1); own check #5 (+1140 / +1144), ran_out -> F;
                 s7 != 0 -> ABORT; live == s6 -> R, else ABORT
     ABORT +1168 __asan_handle_no_return (= pi_abort F_check_reject_clean_starved); unreachable (the text has no abort
                 arm): refuted by the injected writes' NULL (s7 = 0) and by live = s6 (every block freed)
   H1's took = 0 arm (beqz s7 at +300) jumps to X1's LAST instruction, beqz doc at +448; H1's lane runs that one
   instruction too and exits to R (doc = 0) or W1 (doc <> 0). The plan's exit list does not name this exit.
   The count == before arms (+500, +984) are refuted, not taken: a whole write makes at least one call
   (PRW_CrsModel.crs_wN_pos, crs_kfull). The three `__asan_report_load1` arms (+388, +612, +1088 = pi_err_sites) are
   refuted by PRW_CrcGen.djb_byte_shadow (the data is addressable, crs_dat).
   THE RAN-OUT CHECKS. Each of the five checks is `lbu a0, g_own_ran_out` (s8 + 540, s8 the auipc value of +452; at
   check #1 the listing's PLdHi of the object atom 13) then `bnez a0` (the OWN arm), then fuzz_alloc_ran_out and `bnez a0`
   (the RAN arm; check #3's is `beqz a0` to Z, so F is its fall-through; a0 is the ledger's g_ran_out). The RAN arms are REFUTED
   (the batch kit): crs_core holds g_ran_out = c_ran C = 0 at every check. crs_from_R / crs_from_F ask the counter facts crs_post needs (crs_cnt_end).
   THE OWN ARMS ARE REFUTED (v3): at each check the lbu reads g_own_ran_out, which the boundary's ledger holds at 0
   (prh_ledger_own, PRH_Base.v), so `bnez a0` at +460 / +508 / +668 / +992 / +1144 (A' 0x8232c / 0x8235c / 0x823fc /
   0x82540 / 0x825d8) is not taken; the cell is kept across the callees before each read by their own texts' ledgers.
   NUMERALS. Register numbers 1, 2, 3, 4, 8 .. 27 and 10 .. 13 are RISC-V names (s0 = 8, s1 = 9, s2 = 18 .. s11 = 27).
   The offsets above are LENGTHs (4 * slot). 128 (the `addi sp, sp, -128` frame and the class-1 fake frame), 32 (the
   realignment, and the struct pj local's offset), 56 (sizeof (struct pj)), 540 (the lbu offset 0x21c from s8) are
   LENGTHs read off the listing; 1 is the frame class __asan_stack_malloc_1 names; 2 ^ 62 is DERIVED (the texts' bounds).
   Address literals appear ONLY in the computation lemmas that check the cut against the image (crs_entry,
   crs_pcs_plan); instruction words appear only in crs_listing_cut / crs_frame_class / crs_listing_own. Every
   definition reads A_prog_sigma / A_prog_base / pa_val or a PrhImg field. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_WalkEnv PRW_CrsModel PRW_CrcGen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- the boundary pcs, as offsets from A_prog_base (DERIVED from the entry; no ADDRESS literal) ---- *)
Definition CRS_PC0 : Z := A_prog_sigma AS_check_reject_clean_starved - A_prog_base.
Definition CRS_PC_E : Z := CRS_PC0.
Definition CRS_PC_H1 : Z := CRS_PC0 + 296.
Definition CRS_PC_X1 : Z := CRS_PC0 + 392.
Definition CRS_PC_W1 : Z := CRS_PC0 + 452.
Definition CRS_PC_H2 : Z := CRS_PC0 + 504.
Definition CRS_PC_X2 : Z := CRS_PC0 + 616.
Definition CRS_PC_F : Z := CRS_PC0 + 680.
Definition CRS_PC_R : Z := CRS_PC0 + 688.
Definition CRS_PC_Z : Z := CRS_PC0 + 944.
Definition CRS_PC_H3 : Z := CRS_PC0 + 1004.
Definition CRS_PC_X3 : Z := CRS_PC0 + 1092.
Definition CRS_PC_ABORT : Z := CRS_PC0 + 1168.
(* the stack_malloc call and the five own checks' `bnez a0` (refuted from the ledger's own cell, header) *)
Definition CRS_PC_SMALLOC : Z := CRS_PC0 + 120.
Definition CRS_PC_OWN1 : Z := CRS_PC0 + 460.
Definition CRS_PC_OWN2 : Z := CRS_PC0 + 508.
Definition CRS_PC_OWN3 : Z := CRS_PC0 + 668.
Definition CRS_PC_OWN4 : Z := CRS_PC0 + 992.
Definition CRS_PC_OWN5 : Z := CRS_PC0 + 1144.

(* the fake frame: __asan_stack_malloc_1 (class 1, 128 bytes), the struct pj local at + 32 *)
Definition CRS_CID : Z := 1.
Definition CRS_OFF_DOC : Z := 32.
(* the own checks' `lbu a0, 540(s8)` *)
Definition CRS_OFF_OWN : Z := 540.

(* ---- computation: the entry, the slots, the frame, the class ---- *)
Lemma crs_entry : A_prog_sigma AS_check_reject_clean_starved = 0x82160 /\
  A_prog_slot AS_check_reject_clean_starved = 736%nat.
Proof. exact A_entry_check_reject_clean_starved. Qed.

Lemma crs_slots :
  Z.to_nat (CRS_PC_E / 4) = 736%nat /\ Z.to_nat (CRS_PC_H1 / 4) = 810%nat /\ Z.to_nat (CRS_PC_X1 / 4) = 834%nat /\
  Z.to_nat (CRS_PC_W1 / 4) = 849%nat /\ Z.to_nat (CRS_PC_H2 / 4) = 862%nat /\ Z.to_nat (CRS_PC_X2 / 4) = 890%nat /\
  Z.to_nat (CRS_PC_F / 4) = 906%nat /\ Z.to_nat (CRS_PC_R / 4) = 908%nat /\ Z.to_nat (CRS_PC_Z / 4) = 972%nat /\
  Z.to_nat (CRS_PC_H3 / 4) = 987%nat /\ Z.to_nat (CRS_PC_X3 / 4) = 1009%nat /\
  Z.to_nat (CRS_PC_ABORT / 4) = 1028%nat /\ Z.to_nat (CRS_PC_SMALLOC / 4) = 766%nat.
Proof. vm_compute. repeat split. Qed.

(* the listing entry at each boundary (the cut is on the listing the engine runs) *)
Lemma crs_listing_cut :
  nth_error A_prog_listing (Z.to_nat (CRS_PC_E / 4)) = Some (PW 0xf8010113) /\          (* addi sp, sp, -128 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_H1 / 4)) = Some (PW 0x50b13) /\            (* mv s6, a0 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_X1 / 4)) = Some (PW 0x20d0c13) /\          (* addi s8, s10, 32 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_W1 / 4)) = Some (PHi (24%bv : bv 5) 18%nat) /\  (* auipc s8 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_H2 / 4)) = Some (PW 0x21cc4503) /\         (* lbu a0, 540(s8) *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_X2 / 4)) = Some (PW 0x1751663) /\          (* bne a0, s7, 12 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_F / 4)) = Some (PW 0xb8513) /\             (* mv a0, s7 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_R / 4)) = Some (PW 0xff800513) /\          (* li a0, -8 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_Z / 4)) = Some (PW 0xe0b9063) /\           (* bnez s7 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_H3 / 4)) = Some (PCall AS_fuzz_alloc_count (1%bv : bv 5)) /\
  nth_error A_prog_listing (Z.to_nat (CRS_PC_X3 / 4)) = Some (PW 0x1751663) /\          (* bne a0, s7, 12 *)
  nth_error A_prog_listing (Z.to_nat (CRS_PC_ABORT / 4)) = Some (PCall AS___asan_handle_no_return (1%bv : bv 5)) /\
  nth_error A_prog_listing (S (Z.to_nat (CRS_PC_ABORT / 4))) = Some (PCall AS_abort (1%bv : bv 5)).
Proof. vm_compute. repeat split. Qed.

(* the frame: `addi a0, zero, 128` then `jal __asan_stack_malloc_1` (class 1), whose frame is 128 bytes *)
Lemma crs_frame_class :
  nth_error A_prog_listing (Z.to_nat (CRS_PC_SMALLOC / 4 - 1)) = Some (PW 0x8000513) /\
  nth_error A_prog_listing (Z.to_nat (CRS_PC_SMALLOC / 4)) = Some (PCall AS___asan_stack_malloc_1 (1%bv : bv 5)) /\
  CRS_CID = 1 /\ fs_frame_bytes CRS_CID = 128.
Proof. vm_compute. repeat split. Qed.

(* the five own reads: check #1 is the listing's PLdHi of the object atom 13 through the hi atom 18 (s8); the
   other four read 540(s8) *)
Lemma crs_listing_own :
  nth_error A_prog_listing (S (Z.to_nat (CRS_PC_W1 / 4))) =
    Some (PLdHi (10%bv : bv 5) (24%bv : bv 5) 18%nat (A_OBJ 13) 0 SZ1 false) /\
  nth_error A_prog_listing (Z.to_nat (CRS_PC_OWN2 / 4 - 1)) = Some (PW 0x21cc4503) /\
  nth_error A_prog_listing (Z.to_nat (CRS_PC_OWN3 / 4 - 1)) = Some (PW 0x21cc4503) /\
  nth_error A_prog_listing (Z.to_nat (CRS_PC_OWN4 / 4 - 1)) = Some (PW 0x21cc4503) /\
  nth_error A_prog_listing (Z.to_nat (CRS_PC_OWN5 / 4 - 1)) = Some (PW 0x21cc4503) /\
  CRS_PC_OWN1 = CRS_PC_W1 + 8 /\ CRS_PC_OWN2 = CRS_PC_H2 + 4.
Proof. vm_compute. repeat split. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).

(* s8 from W1 on: the auipc value, g_own_ran_out - 540 (a PrhImg field less the lbu's offset) *)
Definition CRS_RO : Z := @pi_g_own_ran_out prh_img_A - CRS_OFF_OWN.
Definition CRS_FRAME : Z := @pi_frame prh_img_A F_check_reject_clean_starved.

(* ---- computation: the cut against the image ---- *)
Lemma crs_pc_entry : BASE + CRS_PC_E = SIGMA AS_check_reject_clean_starved.
Proof. vm_compute. reflexivity. Qed.
Lemma crs_pc_abort_is_pi : BASE + CRS_PC_ABORT = @pi_abort prh_img_A F_check_reject_clean_starved.
Proof. vm_compute. reflexivity. Qed.
(* pi_frame = 128 + the realignment slack 32 - 16 *)
Lemma crs_frame_is_pi : CRS_FRAME = 128 + 32 - 16.
Proof. vm_compute. reflexivity. Qed.
(* the three report arms are the generated error sites *)
Lemma crs_err_sites : @pi_err_sites prh_img_A F_check_reject_clean_starved =
  [BASE + CRS_PC0 + 388; BASE + CRS_PC0 + 612; BASE + CRS_PC0 + 1088].
Proof. vm_compute. reflexivity. Qed.
(* H1 is fuzz_alloc_live's first return site, R is the fuzz_free return site of F *)
Lemma crs_pc_H1_ret : In (BASE + CRS_PC_H1)
  (@pi_call_rets prh_img_A F_check_reject_clean_starved F_fuzz_alloc_live).
Proof. vm_compute. left. reflexivity. Qed.
Lemma crs_pc_R_ret : In (BASE + CRS_PC_R)
  (@pi_call_rets prh_img_A F_check_reject_clean_starved F_fuzz_free).
Proof. vm_compute. right. left. reflexivity. Qed.
(* s8: the hi atom 18 is g_own_ran_out - 540, the object atom 13 is g_own_ran_out *)
Lemma crs_ro_atoms : VAL (A_HI 18) = CRS_RO /\ VAL (A_OBJ 13) = @pi_g_own_ran_out prh_img_A.
Proof. vm_compute. split; reflexivity. Qed.
(* the plan's addresses (the internal file SEGMENT-PLAN-Aprime.md), the one place they are written *)
Lemma crs_pcs_plan :
  BASE + CRS_PC_E = 0x82160 /\ BASE + CRS_PC_H1 = 0x82288 /\ BASE + CRS_PC_X1 = 0x822e8 /\
  BASE + CRS_PC_W1 = 0x82324 /\ BASE + CRS_PC_H2 = 0x82358 /\ BASE + CRS_PC_X2 = 0x823c8 /\
  BASE + CRS_PC_F = 0x82408 /\ BASE + CRS_PC_R = 0x82410 /\ BASE + CRS_PC_Z = 0x82510 /\
  BASE + CRS_PC_H3 = 0x8254c /\ BASE + CRS_PC_X3 = 0x825a4 /\ BASE + CRS_PC_ABORT = 0x825f0 /\
  BASE + CRS_PC_SMALLOC = 0x821d8 /\
  BASE + CRS_PC_OWN1 = 0x8232c /\ BASE + CRS_PC_OWN2 = 0x8235c /\ BASE + CRS_PC_OWN3 = 0x823fc /\
  BASE + CRS_PC_OWN4 = 0x82540 /\ BASE + CRS_PC_OWN5 = 0x825d8 /\
  CRS_RO = 0x5dd324 /\ CRS_RO + CRS_OFF_OWN = 0x5dd540.
Proof. vm_compute. repeat split. Qed.

(* ---- the list and count arithmetic the boundaries need ---- *)

(* Ledger.lsum under a permutation (the live checks: fuzz_alloc_live = s6) *)
Lemma crs_lsum_perm : forall l l', Permutation l l' -> Ledger.lsum l = Ledger.lsum l'.
Proof.
intros l l' H. induction H as [|x l1 l2 H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2].
- reflexivity.
- destruct x as [a k]. cbn [Ledger.lsum]. lia.
- destruct x as [a k]. destruct y as [b m]. cbn [Ledger.lsum]. lia.
- rewrite IH1. exact IH2.
Qed.

Lemma crs_count_le_length : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.

(* THE CAPACITY FACT of the E lane: aj_stack_malloc_at_x's `count_cid cid (frames Sc) < fs_frames cid` at cid = 1,
   from the text's frames premise (29 frames at most, against the class's 8192) *)
Lemma crs_cap : forall S,
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_reject_clean_starved ->
  count_cid 1 (frames S) < fs_frames 1.
Proof.
intros S H. pose proof (crs_count_le_length 1 (frames S)) as Hc.
assert (E1 : ck_FRAMES_CAP - FR_check_reject_clean_starved = 29) by (vm_compute; reflexivity).
assert (E2 : fs_frames 1 = 8192) by (vm_compute; reflexivity).
lia.
Qed.

(* the callees' frame bounds once the function's own frame is pushed: pj_parse's `frames + DOC_D <= fs_frames 0`
   and its ck_FRAMES_CAP - FR_pj_parse, pj_write's `frames < fs_frames 0` *)
Lemma crs_cap_callee : forall S S3 pos,
  frames S3 = (CRS_CID, pos) :: frames S ->
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
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_A) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_A)).

(* THE STAGE RECORD: the text's binders (the model-run position rp_*, the entry state, the input, the tree, the
   ledger and g_most) and the position __asan_stack_malloc_1 returned. The old kit's margin c_kr is gone (the new
   text states room as room_live_cf); c_most and the rp_* position are new. The flag reads of the five checks are
   path-local (each arm's register a0), so they are premises of the predicates, not fields. c_dp / c_ws are the
   journal's moved entry depot and the wild budget spent (CrsKitBp.v's cb_dp / cb_ws). *)
Record crsC : Type := mkCrsC {
  c_ly : alayout; c_S : astate; c_Hp : list Z; c_W : world SEGS;
  c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model; c_ch : list (Z * Z * Z);
  c_data : Z; c_tb : list Z; c_took : Z; c_doc : Z; c_t : PjTree.jv; c_D : list (Z * Z);
  c_Lam : list (Z * Z); c_peak : Z; c_cnt : Z; c_ran : Z; c_most : Z;
  c_rp_x : list Z; c_rp_os : list (option nat * option nat * option nat);
  c_rp_i : nat; c_rp_H0 : list Z; c_rp_hist : list YG00.chunk;
  c_fpos : Z;                          (* the position __asan_stack_malloc_1 returned *)
  (* THE WILD BUDGET OF THE WALK (the text's post is fpostFbm (wbudget [] (prh_wk F_check_reject_clean_starved))
     because pj_parse's cursor traces are WILD at A' under the repaired prh_cw_pj - parse_items' free stores a trace
     at the cursor end, parse_string's at the slot word). The walk keeps every boundary journal at the EMPTY budget,
     from the entry state with its depot replaced by c_dp (YCbqGwild.ajournal_xw_rebaseR at wle' RZ_cf, at X1 after pj_parse);
     c_ws is the budget spent so far, which covers the moved depot's wild part from the entry's (crs_dpok). R gives
     the journal back at c_ws (YCbqGwild.ajournal_xw_unbase0R at wle' RZ_cf). Before X1: c_dp = the entry depot, c_ws = []. *)
  c_dp : list (list Z); c_ws : list (list Z)
}.

(* the context with the frame position set: the prologue learns c_fpos only from the frame call, so the E lane
   proves crs_from_E C from crs_from_H1 (crs_with_fpos C p) for every p the call may return; the journal's entry
   depot is the entry's own there, at the empty budget *)
Definition crs_with_fpos (C : crsC) (p : Z) : crsC :=
  mkCrsC (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_regs C) (c_mem C) (c_md C) (c_ch C) (c_data C) (c_tb C) (c_took C)
    (c_doc C) (c_t C) (c_D C) (c_Lam C) (c_peak C) (c_cnt C) (c_ran C) (c_most C)
    (c_rp_x C) (c_rp_os C) (c_rp_i C) (c_rp_H0 C) (c_rp_hist C) p (st_depot (c_S C)) [].
(* the context after a rebase: the journal's entry depot moved to d, the budget spent so far ws *)
Definition crs_with_dp (C : crsC) (d ws : list (list Z)) : crsC :=
  mkCrsC (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_regs C) (c_mem C) (c_md C) (c_ch C) (c_data C) (c_tb C) (c_took C)
    (c_doc C) (c_t C) (c_D C) (c_Lam C) (c_peak C) (c_cnt C) (c_ran C) (c_most C)
    (c_rp_x C) (c_rp_os C) (c_rp_i C) (c_rp_H0 C) (c_rp_hist C) (c_fpos C) d ws.

Definition cSize (C : crsC) : Z := Z.of_nat (length (c_tb C)).
(* the frame, at the ENTRY layout (alx_layout gives the same address at every later layout of the journal) *)
Definition cF (C : crsC) : Z := frame_addr (c_ly C) CRS_CID (c_fpos C).
Definition cOut (C : crsC) : Z := cF C + CRS_OFF_DOC.
Definition cHash (C : crsC) : Z := ck_djb2 5381 (c_tb C).
Definition cN1 (C : crsC) : Z := PjWriteHyp.wcalls (c_t C) true.
Definition cN0 (C : crsC) : Z := PjWriteHyp.wcalls (c_t C) false.

(* ---- THE RUN EVENTS (the text's ck_crcs_evs, PRH_FnCheck.v blob 0d50b048d570) and their parts, in the order the
   body makes them: the starved reading, then with a tree for p = pretty and p = compact the whole write (w_evs), the
   fuzz_free of its text (w_free), the injected write (w_starved at the model's pick; its chosen failure makes no
   event). The F site's fuzz_free (s7) makes none: s7 = NULL whenever no allocation was refused. ---- *)
Definition crs_evs (C : crsC) : list PresetReqAt.hev :=
  ck_crcs_evs ReaderRes.jr_strtod (c_tb C) (c_took C) (c_doc C) (c_t C).
Definition crs_ev_sp (C : crsC) : list PresetReqAt.hev :=
  PresetReqAt.starved_parse ReaderRes.jr_strtod (c_tb C) (Z.to_nat (c_took C)).
Definition crs_ev_w (C : crsC) (p : bool) : list PresetReqAt.hev := PresetReqAt.w_evs (c_t C) p.
Definition crs_ev_wf (C : crsC) (p : bool) : list PresetReqAt.hev := PresetReqAt.w_free (c_t C) p.
Definition crs_ev_ws (C : crsC) (p : bool) : list PresetReqAt.hev :=
  PresetReqAt.w_starved (c_t C) p (PresetReqAt.pick (c_tb C) (PresetReqAt.wcalls (c_t C) p)).
(* the prefix of crs_evs consumed at each boundary (when nothing was refused) *)
Definition crs_evs_at_E (C : crsC) : list PresetReqAt.hev := [].
Definition crs_evs_at_H1 (C : crsC) : list PresetReqAt.hev := [].
Definition crs_evs_at_X1 (C : crsC) : list PresetReqAt.hev := [].
Definition crs_evs_at_W1 (C : crsC) : list PresetReqAt.hev := crs_ev_sp C.
Definition crs_evs_at_H2 (C : crsC) : list PresetReqAt.hev := crs_evs_at_W1 C ++ crs_ev_w C true ++ crs_ev_wf C true.
Definition crs_evs_at_X2 (C : crsC) : list PresetReqAt.hev := crs_evs_at_H2 C.
Definition crs_evs_at_Z (C : crsC) : list PresetReqAt.hev := crs_evs_at_X2 C ++ crs_ev_ws C true.
Definition crs_evs_at_H3 (C : crsC) : list PresetReqAt.hev := crs_evs_at_Z C ++ crs_ev_w C false ++ crs_ev_wf C false.
Definition crs_evs_at_X3 (C : crsC) : list PresetReqAt.hev := crs_evs_at_H3 C.
Definition crs_evs_at_F (C : crsC) : list PresetReqAt.hev := crs_evs C.
Definition crs_evs_at_R (C : crsC) : list PresetReqAt.hev := crs_evs C.

(* ---- the text's premises (tcheck_reject_clean_starved_specX, lib/A/PRH_FnCheck.v:1756-1838),
   same order and spelling; CTX0 is the text's own parameter (no DW, :1756); the run's strtod model is
   KEYED to ReaderRes.jr_strtod (:1778, :1796; no rp_sm binder); the five premises after ck_frm0 are the run's
   call bound (:1799), the wild room (:1802), the two room counts (:1820-1823) and the consumer window (:1838). ---- *)
Definition crs_pre (CTX0 : list (list Z)) (C : crsC) : Prop :=
  fpre B ARx STK (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_regs C) (c_mem C) (c_md C) (c_ch C) /\
  YAkMemnorm.memnorm SEGS (c_mem C) /\
  prh_univ_closure B CTX0 /\ prh_ctx CTX0 F_check_reject_clean_starved (raZ (c_regs C) :: spine (c_ch C)) /\
  getr (c_regs C) 10 = w64 (c_data C) /\ getr (c_regs C) 11 = w64 (cSize C) /\
  getr (c_regs C) 12 = w64 (c_took C) /\ getr (c_regs C) 13 = w64 (c_doc C) /\
  cSize C <= 3 * 2 ^ 20 /\ 0 < c_data C /\ c_data C + cSize C < 2 ^ 62 /\
  src_rd (c_W C) (c_mem C) (c_data C) (c_tb C) /\
  PRH_FnReader.prhReader_home B (c_ly C) (c_S C) (c_Hp C) (c_Lam C) (c_data C) (cSize C) /\
  0 <= c_took C <= ck_ncalls (c_tb C) /\
  (c_doc C = 0 \/
   (ck_read (c_tb C) = Some (c_t C) /\
    ck_tree_ok (c_ly C) (c_S C) (c_Lam C) (c_W C) (c_mem C) (c_doc C) (c_t C) (c_D C) /\
    PjWriteHyp.wlen (c_t C) false + 1 < 2 ^ 24 /\ PjWriteHyp.wlen (c_t C) true + 1 < 2 ^ 28 /\
    (PjTree.depth (c_t C) <= 32)%nat)) /\
  LEDGER (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_Lam C) (c_peak C) (c_cnt C) SIZE_MAXZ (c_ran C) (c_most C) 0 /\
  c_cnt C < 2 ^ 62 - 2 ^ 30 /\
  prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) (crs_evs C) /\
  c_ran C = 0 /\
  PRH_FnPj.RQ_pj_parse (c_tb C) <= c_most C /\
  (c_doc C <> 0 -> RQW (c_t C) true <= c_most C /\ RQW (c_t C) false <= c_most C) /\
  blocks_bytes (c_S C) + LIVE_check_reject_clean_starved (c_tb C) (c_t C) <= LIVE_MAX /\
  RQ_crcs (c_tb C) + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames (c_S C))) <= ck_FRAMES_CAP - FR_check_reject_clean_starved /\
  room_live_cf (c_S C) /\
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) (c_rp_H0 C) (c_rp_hist C) (c_S C) /\
  ck_frm0 (fx := fx) /\
  (length (c_rp_os C) <= 4)%nat /\
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_reject_clean_starved) (st_depot (c_S C)) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (c_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (c_tb C) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (c_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (c_tb C) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) (length (crs_evs C)).

(* ---- the text's conclusion (PRH_FnCheck.v:1840-1858), no abort arm, with the EXACT advance under
   ran' = 0, conjunct for conjunct in the text's order (the cut adds `ran' = ran`, :1848). g_most and g_own_ran_out
   are the ledger's last two arguments: most is kept and the own cell ends 0, as at entry. crs_post is the text's
   budgeted post fpostFbm (wbudget [] (prh_wk F_check_reject_clean_starved)) (:1841): pj_parse's cursor traces are
   WILD at A' under the repaired prh_cw_pj (the record's comment), and R unbases the walk's journal into it. ---- *)
Definition crs_Q (C : crsC)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    room_live_cf S' /\ exists Lam' peak' cnt' ran',
    Permutation Lam' (c_Lam C) /\ Permutation (ablocks B ly' S') (ablocks B (c_ly C) (c_S C)) /\
    c_peak C <= peak' /\
    c_cnt C <= cnt' <= c_cnt C + ck_crcs_max (c_tb C) (c_took C) (c_doc C) (c_t C) /\
    (ran' = c_ran C \/ ran' = 1) /\
    ran' = c_ran C /\
    (ran' = 0 -> cnt' = c_cnt C + ck_crcs_growth (c_tb C) (c_took C) (c_doc C) (c_t C)) /\
    (ran' = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
       (c_rp_i C + length (crs_evs C))%nat (c_rp_H0 C) hist' S') /\
    LEDGER ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' (c_most C) 0 /\
    PRH_Base.bytes_at W' mem' (c_data C) (c_tb C) /\
    (c_doc C <> 0 -> pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') (c_doc C) (c_t C) (c_D C)).
Definition crs_post (C : crsC) : world SEGS -> config -> Prop :=
  fpostFbm (fx := fx) B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_reject_clean_starved)) STK [] (c_regs C)
    (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) (crs_Q C).

(* ---- a boundary: the machine state at a pc, its float state fxk (pj_parse's strtod may change it) ---- *)
Definition crs_cfg (fxk : YK11.FPState) (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) : config :=
  mkCfg (@YK11.mkst fxk regs (w64 pc) mem (YK11.seg_rom SEGS)) md.
Definition crs_regsat (regs : bvmap 5 word) (l : list (bv 5 * Z)) : Prop :=
  Forall (fun p => getr regs (fst p) = w64 (snd p)) l.

(* the journal from entry, with the function's own class-1 frame in `own`, at the EMPTY budget from the entry state
   with its depot moved to c_dp C (the record's comment) *)
Definition crs_J (C : crsC) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  AJ STK (spZ (c_regs C)) [] (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C)
     [(CRS_CID, c_fpos C)] ly3 S3 Hp3 W3 mem3 md3 k.
(* the moved depot's wild part is covered from the entry's by the budget spent, and that budget is within the text's *)
Definition crs_dpok (C : crsC) : Prop :=
  YCbqGwild.wbudget [] (prh_wk F_check_reject_clean_starved) (c_ws C) /\
  incl (wild_part (as_universe B) (c_dp C)) (wild_part (as_universe B) (st_depot (c_S C)) ++ c_ws C).

(* the same journal over a world relation R (the journal's conjunct 4 is R W W'): crs_J is crs_JR at wle (crs_J_R_wle);
   a cut after a free or a realloc carries crs_JR at the re-hiding relation, and crs_JR_mono moves a journal from a
   smaller relation to a larger one (wle to wle' by wle_wle') *)
Definition crs_JR (R : world SEGS -> world SEGS -> Prop) (C : crsC) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (W3 : world SEGS) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  ajournal_xR (SK := SK) SEGS B PST ARx R STK (spZ (c_regs C)) [] (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C)
     (c_W C) (c_mem C) (c_md C) [(CRS_CID, c_fpos C)] ly3 S3 Hp3 W3 mem3 md3 k.
Lemma crs_J_R_wle : forall C ly3 S3 Hp3 W3 mem3 md3 k,
  crs_J C ly3 S3 Hp3 W3 mem3 md3 k = crs_JR (@wle SEGS) C ly3 S3 Hp3 W3 mem3 md3 k.
Proof. reflexivity. Qed.
Lemma crs_JR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall C ly3 S3 Hp3 W3 mem3 md3 k, crs_JR R1 C ly3 S3 Hp3 W3 mem3 md3 k -> crs_JR R2 C ly3 S3 Hp3 W3 mem3 md3 k.
Proof.
intros R1 R2 H12 C ly3 S3 Hp3 W3 mem3 md3 k HJ. unfold crs_JR, ajournal_xR, ajournal_xwR in *.
exact (ajournal_xbR_mono (SK := SK) SEGS B PST ARx R1 R2 H12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* THE THIRTEEN SAVED WORDS: `addi sp, sp, -128`, `sd zero, 0(sp)` (the probe), then `sd ra, 120(sp)`, `sd s0,
   112(sp)` .. `sd s11, 24(sp)` (slots 737-750); R reads them back from s0 - 128, so a boundary carries the SLOTS *)
Definition CRS_SAVED : list (Z * bv 5) :=
  [(120, 1%bv); (112, 8%bv); (104, 9%bv); (96, 18%bv); (88, 19%bv); (80, 20%bv); (72, 21%bv);
   (64, 22%bv); (56, 23%bv); (48, 24%bv); (40, 25%bv); (32, 26%bv); (24, 27%bv)].
Definition crs_saved (C : crsC) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  Forall (fun p : Z * bv 5 =>
            rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs C) - 128 + fst p)
            = Some (bv_unsigned (getr (c_regs C) (snd p))))
    CRS_SAVED.

(* the frame the prologue holds: pushed on the entry frames, its flag word (R's `ld a0, 120(s2)`, `sb zero, 0(a0)`)
   at the CURRENT layout (aj_flag_store_x's form), its bytes present *)
Definition crs_frame (C : crsC) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (mem3 : word -> option byte) : Prop :=
  frames S3 = (CRS_CID, c_fpos C) :: frames (c_S C) /\
  rdword (aview SEGS (w_H W3) mem3) (cF C + fs_frame_bytes CRS_CID - 8)
    = Some (flag_addr ly3 CRS_CID (c_fpos C)) /\
  (forall a, cF C <= a < cF C + fs_frame_bytes CRS_CID -> apresent (w_H W3) mem3 a).

(* the 56-byte struct pj at F + 32 is unpoisoned: E's sixteen shadow pokes (slots 792-808; slot 796 is `li a0, -13`) leave shadow
   [F, F + 32) = f1, [F + 32, F + 88) = 0, [F + 88, F + 128) = f3 *)
Definition crs_slot (C : crsC) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (cOut C) 56 /\
  shadow_hull_vis (aview SEGS (w_H W3) mem3) (cOut C) 56.

(* THE MODEL-RUN POSITION AT A BOUNDARY, EXACT: evs is the prefix of crs_evs the body has made there
   (crs_evs_at_<SEG>). Stated only when nothing was refused (ran3 = 0): after a refusal the instance has freed blocks
   the all-granted run still holds, so no position of the run describes the state (the text's note on its post). *)
Definition crs_pos (C : crsC) (evs : list PresetReqAt.hev) (ran3 : Z) (S3 : astate) : Prop :=
  ran3 = 0 -> exists rp_hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
    (c_rp_i C + length evs)%nat (c_rp_H0 C) rp_hist' S3.

(* the ledger, the counters, the room and the position at a boundary (evs: that boundary's crs_evs_at_<SEG>).
   g_ran_out is the entry's at every boundary (ran3 = c_ran C): the cut's post states `ran' = ran` (PRH_FnCheck.v:1848),
   since no allocation of the body is REFUSED - pj_write's post states prh_granted (DEAD-PJWRITE, PRH_FnWriter.v:1198),
   the starved reading's is tpj_parse_specX's guarded conjunct (PRH_FnPj.v:736-754), and the chosen failures leave g_ran_out alone *)
Definition crs_core (C : crsC) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (Lam3 : list (Z * Z)) (peak3 cnt3 ran3 : Z) (evs : list PresetReqAt.hev) : Prop :=
  LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (c_most C) 0 /\
  c_peak C <= peak3 /\ ran3 = c_ran C /\ c_cnt C <= cnt3 /\ cnt3 < 2 ^ 62 /\
  room_live_cf S3 /\ crs_pos C evs ran3 S3.
(* Lam and the allocator blocks back as they were: the starved reading is refused (it frees its blocks), each whole
   write's text is freed by fuzz_free, each injected write gives NULL and frees its buffer *)
Definition crs_perm (C : crsC) (ly3 : alayout) (S3 : astate) (Lam3 : list (Z * Z)) : Prop :=
  Permutation Lam3 (c_Lam C) /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly C) (c_S C)).
Definition crs_live (C : crsC) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (Lam3 : list (Z * Z)) (peak3 cnt3 ran3 : Z) (evs : list PresetReqAt.hev) : Prop :=
  crs_core C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 ran3 evs /\ crs_perm C ly3 S3 Lam3.
(* the input bytes and their shadow (the three hash loops' memory facts, PRW_CrcGen.djb_head) *)
Definition crs_dat (C : crsC) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (Lam3 : list (Z * Z)) : Prop :=
  PRH_Base.bytes_at W3 mem3 (c_data C) (c_tb C) /\
  PRH_FnReader.prhReader_home B ly3 S3 Hp3 Lam3 (c_data C) (cSize C) /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (c_data C) (cSize C) /\
  (0 < cSize C -> shadow_hull_vis (aview SEGS (w_H W3) mem3) (c_data C) (cSize C)).

(* the document, still the tree the text names *)
Definition crs_tree (C : crsC) (ly3 : alayout) (S3 : astate) (Lam3 : list (Z * Z)) (W3 : world SEGS)
  (mem3 : word -> option byte) : Prop :=
  c_doc C <> 0 -> ck_tree_ok ly3 S3 Lam3 W3 mem3 (c_doc C) (c_t C) (c_D C).

(* what every boundary after the prologue carries *)
Definition crs_base (CTX0 : list (list Z)) (C : crsC) (fxk : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k sp2 : Z) : Prop :=
  crs_pre CTX0 C /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  crs_J C ly3 S3 Hp3 W3 mem3 md3 k /\
  crs_frame C ly3 S3 W3 mem3 /\ crs_saved C W3 mem3 /\ crs_slot C W3 mem3 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W3) mem3) /\
  YAkMemnorm.memnorm SEGS mem3 /\
  getr regs3 3 = getr (c_regs C) 3 /\ getr regs3 4 = getr (c_regs C) 4 /\
  spZ (c_regs C) - CRS_FRAME <= sp2 /\ sp2 <= spZ (c_regs C) - 128 /\ sp2 mod 32 = 0 /\
  crs_dpok C.

(* the same boundary fact over a world relation R (its journal is crs_JR R): crs_base is crs_baseR at wle
   (crs_base_R_wle); a boundary after a free or a realloc carries crs_baseR at the re-hiding relation *)
Definition crs_baseR (R : world SEGS -> world SEGS -> Prop) (CTX0 : list (list Z)) (C : crsC) (fxk : YK11.FPState)
  (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte)
  (md3 : Model) (k sp2 : Z) : Prop :=
  crs_pre CTX0 C /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  crs_JR R C ly3 S3 Hp3 W3 mem3 md3 k /\
  crs_frame C ly3 S3 W3 mem3 /\ crs_saved C W3 mem3 /\ crs_slot C W3 mem3 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W3) mem3) /\
  YAkMemnorm.memnorm SEGS mem3 /\
  getr regs3 3 = getr (c_regs C) 3 /\ getr regs3 4 = getr (c_regs C) 4 /\
  spZ (c_regs C) - CRS_FRAME <= sp2 /\ sp2 <= spZ (c_regs C) - 128 /\ sp2 mod 32 = 0 /\
  crs_dpok C.
Lemma crs_base_R_wle : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  crs_base CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 =
  crs_baseR (@wle SEGS) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2.
Proof. reflexivity. Qed.
Lemma crs_baseR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  crs_baseR R1 CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_baseR R2 CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2.
Proof.
intros R1 R2 H12 CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 (HP & H1 & H2 & HJ & Hrest).
exact (conj HP (conj H1 (conj H2 (conj (crs_JR_mono R1 R2 H12 _ _ _ _ _ _ _ _ HJ) Hrest)))).
Qed.

(* ---- the register sets (the plan's roles) ---- *)
(* sp and s1 the realigned sp, s0 the entry sp, s2 and s10 the fake frame (s2 <> 0, so s10 = s2), s11 the shadow
   offset (`ld s11, 0(a1)` through the GOT word) *)
Definition crs_rbase (C : crsC) (sp2 : Z) : list (bv 5 * Z) :=
  [(2%bv, sp2); (8%bv, spZ (c_regs C)); (9%bv, sp2); (18%bv, cF C); (26%bv, cF C); (27%bv, SHADOW_OFF)].
(* s9, the frame's shadow (`srli s9, s10, 3`; `add s9, s9, s11`) *)
Definition crs_rsh (C : crsC) : list (bv 5 * Z) := [(25%bv, shadow_addr (cF C))].
(* s3 = doc, s4 = size, s5 = data (until L3 eats s4 and s5) *)
Definition crs_rargs (C : crsC) : list (bv 5 * Z) :=
  [(19%bv, c_doc C); (20%bv, cSize C); (21%bv, c_data C)].
(* s6 = fuzz_alloc_live () at entry *)
Definition crs_rlive (C : crsC) : list (bv 5 * Z) := [(22%bv, Ledger.lsum (c_Lam C))].
(* s8 from W1's auipc on: the ran-out cell base *)
Definition crs_rro : list (bv 5 * Z) := [(24%bv, CRS_RO)].

(* ---- the counter arithmetic ---- *)
(* the starved reading's share of the growth *)
Definition crs_first (C : crsC) : Z :=
  if c_took C =? 0 then 0 else ck_pick (c_tb C) (c_took C) + 1.
(* g_count after the starved reading (exact once check #1 passed), after the pretty pair, after the compact pair *)
Definition crs_cnt1 (C : crsC) : Z := c_cnt C + crs_first C.
Definition crs_cnt2 (C : crsC) : Z := crs_cnt1 C + cN1 C + ck_pick (c_tb C) (cN1 C) + 1.
Definition crs_cnt3 (C : crsC) : Z := crs_cnt2 C + cN0 C + ck_pick (c_tb C) (cN0 C) + 1.
(* after the starved reading: nothing when took = 0, else one more than the injected failure's index at most *)
Definition crs_cnt_R (C : crsC) (cnt1 ran1 : Z) : Prop :=
  (c_took C = 0 -> cnt1 = c_cnt C) /\
  (c_took C <> 0 -> c_cnt C + 1 <= cnt1 <= c_cnt C + ck_pick (c_tb C) (c_took C) + 1 /\
                    (ran1 = 0 -> cnt1 = c_cnt C + ck_pick (c_tb C) (c_took C) + 1)).
(* a whole write of the tree, pretty (p = true) or compact: at least one call, all of them when nothing was
   refused *)
Definition crs_kfull (C : crsC) (p : bool) (kk ranp : Z) : Prop :=
  1 <= kk <= PjWriteHyp.wcalls (c_t C) p /\ (ranp = 0 -> kk = PjWriteHyp.wcalls (c_t C) p).
(* what R and F need of the count: crs_post's bound and growth *)
Definition crs_cnt_end (C : crsC) (cnt3 ran3 : Z) : Prop :=
  cnt3 <= c_cnt C + ck_crcs_max (c_tb C) (c_took C) (c_doc C) (c_t C) /\
  (ran3 = 0 -> cnt3 = c_cnt C + ck_crcs_growth (c_tb C) (c_took C) (c_doc C) (c_t C)).

(* ======================================================================================================== *)
(* ---- THE CONTINUATION PREDICATES, one per segment entry, from the last one backwards. Each is stated over
   (C, the state at its pc) and concludes crs_post C. Lane lemma shapes:
     R: crs_from_R            F: crs_from_R -> crs_from_F
     X3: crs_from_F -> crs_from_R -> crs_from_X3        H3: crs_from_X3 -> crs_from_H3
     Z: crs_from_R -> crs_from_H3 -> crs_from_Z         X2: crs_from_F -> crs_from_Z -> crs_from_X2
     H2: crs_from_R -> crs_from_X2 -> crs_from_H2       W1: crs_from_R -> crs_from_H2 -> crs_from_W1
     X1: (forall d ws, crs_from_R (crs_with_dp C d ws)) -> (forall d ws, crs_from_W1 (crs_with_dp C d ws)) -> crs_from_X1 C
     H1: crs_from_X1 -> crs_from_R -> crs_from_W1 -> crs_from_H1     E: (forall p, crs_from_H1 (crs_with_fpos C p)) -> crs_from_E C ---- *)

(* R (+688): `sb -8` over the local's shadow bytes 4-10, the retired magic at F, then (s2 <> 0) `sb -11` over all
   sixteen shadow bytes and the flag release (the byte at the word at s2 + 120 set to 0) (aj_flag_store_xR at wle' RZ_cf); the s2 = 0 arm (+816 .. +876) is
   refuted by s2 = F <> 0; the restores from s0 - 128; ret. Reached by: X1's doc = 0 arm, W1 / H2 / Z's ran-out arms,
   F, X3's live == s6 arm (and H1's took = 0, doc = 0 arm). *)
Definition crs_from_R (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt3 ran3,
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C) ->
  crs_live C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 ran3 (crs_evs_at_R C) ->
  PRH_Base.bytes_at W3 mem3 (c_data C) (c_tb C) ->
  crs_tree C ly3 S3 Lam3 W3 mem3 ->
  crs_cnt_end C cnt3 ran3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_R) regs3 mem3 md3) (crs_post C).

(* F (+680): fuzz_free (s7), then R. Its entries are the OWN and RAN arms of checks #3 (X2: +668 / +676) and #5 (X3: +1144 /
   +1152), all refuted on the batch kit (own = 0 by the ledger, header; crs_core's ran3 = c_ran C = 0), so F is entered with
   ran3 = 1 only vacuously (fuzz_alloc_ran_out returned the ledger's g_ran_out <> 0). The injected write then refused an allocation, so the writer post is on its
   FAILED arm (w_failed <> 0): s7 = q = 0 and Lam / the blocks are back (crs_perm). No position is asked: after a
   refusal tpj_write_specX states none (it states its advance only under prh_granted), and crs_pos is vacuous at
   ran3 = 1; the NULL free goes through the walk's position-free interim for fuzz_free (NULL). *)
Definition crs_from_F (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt3 ran3 q,
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ [(23%bv, q)]) ->
  crs_core C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 ran3 (crs_evs_at_F C) ->
  ran3 = 1 -> q = 0 -> crs_perm C ly3 S3 Lam3 ->
  PRH_Base.bytes_at W3 mem3 (c_data C) (c_tb C) ->
  crs_tree C ly3 S3 Lam3 W3 mem3 ->
  crs_cnt_end C cnt3 ran3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_F) regs3 mem3 md3) (crs_post C).

(* X3 (+1092): a0 = the count after the whole compact write, s7 = the count before it, a2 = the hash;
   fail (h % N0) (the count == s7 arm, a0 = 0, is refuted: N0 >= 1); pj_write (doc, 0) -> s7 (NULL: the injected
   failure is reached); fail (-1); check #5: OWN arm -> F (refuted: own = 0, header), RAN arm refuted (ran = 0); `bnez s7` -> ABORT refuted
   (s7 = 0); fuzz_alloc_live == s6 -> R (crs_lsum_perm), else ABORT refuted. s4 / s5 are dead (L3 ate them). *)
Definition crs_from_X3 (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  c_doc C <> 0 ->
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ [(19%bv, c_doc C)] ++ crs_rlive C ++ crs_rro
                    ++ [(23%bv, crs_cnt2 C); (10%bv, crs_cnt2 C + cN0 C); (12%bv, cHash C)]) ->
  crs_live C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt2 C + cN0 C) 0 (crs_evs_at_X3 C) ->
  PRH_Base.bytes_at W3 mem3 (c_data C) (c_tb C) ->
  crs_tree C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_X3) regs3 mem3 md3) (crs_post C).

(* H3 (+1004): count (a0), then the third djb2 loop L3 over data (it EATS s4 and s5: `addi s4, s4, -1`,
   `addi s5, s5, 1`), its report arm (+1088) refuted. s7 = the count before the whole compact write; check #4 passed,
   so that write made all N0 calls. *)
Definition crs_from_H3 (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  c_doc C <> 0 ->
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro
                    ++ [(23%bv, crs_cnt2 C)]) ->
  crs_live C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt2 C + cN0 C) 0 (crs_evs_at_H3 C) ->
  crs_dat C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_H3) regs3 mem3 md3) (crs_post C).

(* Z (+944): s7 = 0 (the injected pretty write's NULL) so `bnez s7` -> ABORT is refuted; fuzz_alloc_live == s6
   (crs_lsum_perm) so `bne` -> ABORT is refuted; count -> s7; pj_write (doc, 0); fuzz_free; count; count == before
   (+984) refuted (crs_kfull); check #4: OWN arm -> R (refuted: own = 0, header), RAN arm refuted (ran = 0); else H3. *)
Definition crs_from_Z (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  c_doc C <> 0 ->
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro ++ [(23%bv, 0)]) ->
  crs_live C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt2 C) 0 (crs_evs_at_Z C) ->
  crs_dat C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_Z) regs3 mem3 md3) (crs_post C).

(* X2 (+616): a0 = the count after the whole pretty write, s7 = the count before it, a2 = the hash; fail (h % N1)
   (the a0 = s7 arm refuted); pj_write (doc, 1) -> s7; fail (-1); check #3: OWN arm -> F (refuted: own = 0, header), RAN arm
   refuted (ran = 0), else Z (s7 = 0, g_ran_out = 0, the injected write made pick + 1 calls). *)
Definition crs_from_X2 (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3,
  c_doc C <> 0 ->
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro
                    ++ [(23%bv, crs_cnt1 C); (10%bv, crs_cnt1 C + cN1 C); (12%bv, cHash C)]) ->
  crs_live C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt1 C + cN1 C) 0 (crs_evs_at_X2 C) ->
  crs_dat C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree C ly3 S3 Lam3 W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_X2) regs3 mem3 md3) (crs_post C).

(* H2 (+504): check #2 (its lbu is H2's first instruction): OWN arm -> R (refuted: own = 0, header), RAN arm refuted (ran = 0); count (a0);
   the second djb2 loop L2 (copies of s4 / s5, a0 kept), its report arm (+612) refuted. s7 = the count before the
   whole pretty write (exact: check #1 passed), which made k1 calls. *)
Definition crs_from_H2 (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 ran3 k1,
  c_doc C <> 0 ->
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro
                    ++ [(23%bv, crs_cnt1 C)]) ->
  crs_live C ly3 S3 Hp3 W3 mem3 Lam3 peak3 (crs_cnt1 C + k1) ran3 (crs_evs_at_H2 C) ->
  crs_dat C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree C ly3 S3 Lam3 W3 mem3 ->
  crs_kfull C true k1 ran3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_H2) regs3 mem3 md3) (crs_post C).

(* W1 (+452): auipc s8 (= CRS_RO, crs_ro_atoms); check #1: OWN arm -> R (refuted: own = 0, header), RAN arm refuted
   (g_ran_out = ran1 = c_ran C = 0); count -> s7; pj_write (doc, 1); fuzz_free (its text); count; count == before (+500) refuted
   (crs_kfull). The reading's count and flag are cnt1 / ran1. *)
Definition crs_from_W1 (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt1 ran1,
  c_doc C <> 0 ->
  crs_baseR (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C) ->
  crs_live C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt1 ran1 (crs_evs_at_W1 C) ->
  crs_dat C ly3 S3 Hp3 W3 mem3 Lam3 -> crs_tree C ly3 S3 Lam3 W3 mem3 ->
  crs_cnt_R C cnt1 ran1 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_W1) regs3 mem3 md3) (crs_post C).

(* X1 (+392): s8 = F + 32 (the local), fuzz_alloc_fail (h % took) (a1 = the hash, s7 = took <> 0), pj_parse (data,
   size, s8) (refused: the injected failure is inside its calls), fuzz_alloc_fail (-1), check_reject_clean (rc, s8,
   s6) (premise: the tcheck_reject_clean_specX), then beqz doc (+448): doc = 0 -> R, else W1. Entered with no
   budget spent (c_ws C = []): pj_parse's room comes from the text's, and its cursor traces are the walk's only wild
   ones; X1 continues at the REBASED context (crs_with_dp). *)
Definition crs_from_X1 (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  c_took C <> 0 -> c_ws C = [] ->
  crs_base CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C
                    ++ [(23%bv, c_took C); (11%bv, cHash C)]) ->
  crs_live C ly3 S3 Hp3 W3 mem3 (c_Lam C) (c_peak C) (c_cnt C) (c_ran C) (crs_evs_at_X1 C) ->
  crs_dat C ly3 S3 Hp3 W3 mem3 (c_Lam C) -> crs_tree C ly3 S3 (c_Lam C) W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_X1) regs3 mem3 md3) (crs_post C).

(* H1 (+296): a0 = fuzz_alloc_live () (= lsum Lam), `mv s6, a0`; beqz took: took = 0 -> X1's beqz doc at +448
   (run here; doc = 0 -> R, else W1 with cnt1 = c_cnt, ran1 = c_ran); a1 = 5381; beqz size -> X1; else the first
   djb2 loop L1 (+328 .. +372), its report arm (+388) refuted; exit X1 with a1 = cHash. *)
Definition crs_from_H1 (CTX0 : list (list Z)) (C : crsC) : Prop :=
  forall fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  c_ws C = [] ->
  crs_base CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C
                    ++ [(23%bv, c_took C); (10%bv, Ledger.lsum (c_Lam C))]) ->
  crs_live C ly3 S3 Hp3 W3 mem3 (c_Lam C) (c_peak C) (c_cnt C) (c_ran C) (crs_evs_at_H1 C) ->
  crs_dat C ly3 S3 Hp3 W3 mem3 (c_Lam C) -> crs_tree C ly3 S3 (c_Lam C) W3 mem3 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (crs_cfg fxk (BASE + CRS_PC_H1) regs3 mem3 md3) (crs_post C).

(* E (+0, the entry, the text's own configuration): the prologue (13 saves, `addi s0, sp, 128`, `andi sp, sp, -32`),
   the use-after-return word (alx_const: 1, so the call is made), __asan_stack_malloc_1 (128) at +120
   (aj_stack_malloc_at_x with crs_cap; the real-stack fallback +132 .. +168 is refuted: the returned frame is not 0,
   alx_frames' in_app), `sd s10, 16(s1)`, the frame header (magic 0x41b58ab3, descriptor, pc), s9, the sixteen
   shadow pokes, fuzz_alloc_live; exit H1. *)
Definition crs_from_E (CTX0 : list (list Z)) (C : crsC) : Prop :=
  crs_pre CTX0 C ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (c_W C)
    (cfg_at SEGS (SIGMA AS_check_reject_clean_starved) (c_regs C) (c_mem C) (c_md C))
    (crs_post C).

(* ======================================================================================================== *)
(* ---- THE TRANSPORT FACTS the segments share (the template's CrsKeep, re-checked against the new text: the reader's
   home, the ledger, the tree's visibility, the entry's fake frames and the doc's object home are stated as in the
   blob 37d8e4d0072e). Derivable from AR_laws_x and ajournal_x's own clauses; proved once (CrsTopAp.v crs_Ap_keep), passed to every lane but R and H1.
   No field for g_own_ran_out or g_most (header). ---- *)
Record CrsKeep : Prop := {
  (* the shadow of a window the reader's home premise names, at any ARx state whose ledger lists Lam *)
  kp_home_sh : forall ly S Hp W mem md Lam peak cnt fail ran most own p n,
    ARx ly S Hp W mem md ->
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    PRH_FnReader.prhReader_home B ly S Hp Lam p n ->
    0 < n -> 0 <= p -> p + n <= YM05.alloc_ceiling ->
    range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\
    shadow_hull_vis (aview SEGS (w_H W) mem) p n;
  (* the home moves with the ledger: a permutation of Lam and of the allocator blocks keeps it *)
  kp_home_move : forall ly S Hp W mem Lam peak cnt fail ran most own ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3
      most3 own3 p n,
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 ->
    Permutation Lam3 Lam -> Permutation (ablocks B ly3 S3) (ablocks B ly S) ->
    PRH_FnReader.prhReader_home B ly S Hp Lam p n -> PRH_FnReader.prhReader_home B ly3 S3 Hp3 Lam3 p n;
  (* the shadow of a tree's blocks, which pj_write asks of a tree it is handed *)
  kp_tree_vis : forall ly S Hp W mem md Lam peak cnt fail ran most own D,
    ARx ly S Hp W mem md ->
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    (forall bk, In bk D -> In bk Lam) -> PRH_FnWriter.prhWriter_tree_vis W mem D;
  (* a fake frame of the ENTRY state keeps its bytes and its shadow bytes across the whole journal (FP = []) *)
  kp_frame_keep : forall STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a,
    AJ STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    In (cid, pos) (frames S) ->
    (in_zr a (frame_rng ly (cid, pos)) \/
     in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a;
  (* so a 56-byte object inside such a frame keeps its home, its addressability and its hull *)
  kp_obj_keep : forall STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p,
    ARx ly S Hp W mem md ->
    AJ STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p;
  (* the same two facts at any world relation R (neither reads the journal's world conjunct): a cut after a free or a
     realloc carries its journal at the re-hiding relation *)
  kp_frame_keepR : forall (R : world SEGS -> world SEGS -> Prop) STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3
    k cid pos a,
    ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    In (cid, pos) (frames S) ->
    (in_zr a (frame_rng ly (cid, pos)) \/
     in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a;
  kp_obj_keepR : forall (R : world SEGS -> world SEGS -> Prop) STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3
    k p,
    ARx ly S Hp W mem md ->
    ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p
}.

(* ======================================================================================================== *)
(* ---- KIT LEMMAS ---- *)

(* moving a state's depot to its own depot changes nothing (the journal's entry before any rebase) *)
Lemma crs_set_depot_id : forall S, YG00.set_depot (st_depot S) S = S.
Proof. intros S. destruct S. reflexivity. Qed.

(* a later layout of the journal keeps the frame's address and its flag address (alx_layout) *)
Lemma crs_ly_keep : forall ly S Hp W mem md ly' cid pos,
  ARx ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
intros ly S Hp W mem md ly' cid pos HAR Hle.
pose proof LAWS as HLY. apply alx_layout in HLY.
destruct (HLY ly S Hp W mem md ly' HAR Hle) as (_ & Hfa & _).
split; [apply Hfa|].
pose proof (Hfa cid pos) as E. unfold frame_addr in E. unfold flag_addr. lia.
Qed.

(* at a boundary: the frame register value cF C is the frame at the current layout too, at any world relation *)
Lemma crs_cF_keepR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k,
  crs_pre CTX0 C -> crs_JR R C ly3 S3 Hp3 W3 mem3 md3 k ->
  frame_addr ly3 CRS_CID (c_fpos C) = cF C /\
  flag_addr ly3 CRS_CID (c_fpos C) = flag_addr (c_ly C) CRS_CID (c_fpos C).
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ.
destruct HP as (HF & _). destruct HF as ((HAR & _) & _).
unfold crs_JR in HJ. destruct HJ as (_ & Hle & _).
exact (crs_ly_keep _ _ _ _ _ _ ly3 CRS_CID (c_fpos C) HAR Hle).
Qed.
Lemma crs_cF_keep : forall CTX0 C ly3 S3 Hp3 W3 mem3 md3 k,
  crs_pre CTX0 C -> crs_J C ly3 S3 Hp3 W3 mem3 md3 k ->
  frame_addr ly3 CRS_CID (c_fpos C) = cF C /\
  flag_addr ly3 CRS_CID (c_fpos C) = flag_addr (c_ly C) CRS_CID (c_fpos C).
Proof. intros CTX0 C ly3 S3 Hp3 W3 mem3 md3 k. rewrite crs_J_R_wle. apply crs_cF_keepR. Qed.

(* THE TWO JOURNAL FACTS AT A MOVED ENTRY DEPOT (crs_J's form; CrsKitBp.v crs_frame_keep_dp_B / crs_obj_keep_dp_B):
   no clause they read looks at the entry depot, so CrsKeep's kp_frame_keep / kp_obj_keep hold of a journal from
   `set_depot d S` with ARx at S; proved here from ajournal_x's clauses and AR_laws_x, at any world relation R (the
   clauses read sit at the same places at every R; the plain names are the instances at wle) *)
Lemma crs_frame_keep_dpR : forall (R : world SEGS -> world SEGS -> Prop)
  STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a,
  ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a.
Proof.
intros R STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a HJ Hin Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
exact (HF cid pos a Hin Ha (inFP_nil a)).
Qed.
Lemma crs_obj_keep_dpR : forall (R : world SEGS -> world SEGS -> Prop)
  STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p,
  ARx ly S Hp W mem md ->
  ajournal_xR (SK := SK) SEGS B PST ARx R STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p.
Proof.
intros R STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p HAR HJ HO.
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
  apply (crs_frame_keep_dpR R STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos _ HJ Hin).
  right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
Qed.
Lemma crs_frame_keep_dp : forall STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a,
  AJ STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a.
Proof. exact (crs_frame_keep_dpR (@wle SEGS)). Qed.
Lemma crs_obj_keep_dp : forall STK0 sp0 ly S d Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p,
  ARx ly S Hp W mem md ->
  AJ STK0 sp0 [] ly (YG00.set_depot d S) Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
  ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p.
Proof. exact (crs_obj_keep_dpR (@wle SEGS)). Qed.

(* the E lane's capacity fact at the entry state *)
Lemma crs_cap_pre : forall CTX0 C, crs_pre CTX0 C -> count_cid 1 (frames (c_S C)) < fs_frames 1.
Proof.
intros CTX0 C H. apply crs_cap.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hfr & _).
exact Hfr.
Qed.

(* the growth at the two ends: the doc = 0 exit after the reading, the normal end after the compact pair *)
Lemma crs_growth_doc0 : forall C, c_doc C = 0 ->
  c_cnt C + ck_crcs_growth (c_tb C) (c_took C) (c_doc C) (c_t C) = crs_cnt1 C.
Proof.
intros C H. unfold ck_crcs_growth, crs_cnt1, crs_first.
assert (E : (c_doc C =? 0) = true) by (apply Z.eqb_eq; exact H).
rewrite E. cbv beta iota. lia.
Qed.
Lemma crs_growth_doc : forall C, c_doc C <> 0 ->
  c_cnt C + ck_crcs_growth (c_tb C) (c_took C) (c_doc C) (c_t C) = crs_cnt3 C.
Proof.
intros C H. unfold ck_crcs_growth, crs_cnt3, crs_cnt2, crs_cnt1, crs_first, cN1, cN0.
assert (E : (c_doc C =? 0) = false) by (apply Z.eqb_neq; exact H).
rewrite E. cbv beta iota. lia.
Qed.

(* ---- THE RUN EVENTS: the entry premise, its split at the boundaries, and the free sites' events ---- *)

(* the entry premise of the text, as crs_pre carries it *)
Lemma crs_run_of_pre : forall CTX0 C, crs_pre CTX0 C ->
  prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) (crs_evs C).
Proof.
intros CTX0 C H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _).
exact Hr.
Qed.

(* the cut's four appended premises, as crs_pre carries them (its last four conjuncts): the wild room, the reading's
   two room counts at the entry, the consumer window over the whole crs_evs *)
Lemma crs_pre_k1 : forall CTX0 C, crs_pre CTX0 C ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_reject_clean_starved) (st_depot (c_S C)) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (c_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (c_tb C) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (c_S C)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (c_tb C) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) (length (crs_evs C)).
Proof.
intros CTX0 C H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & Hw & Hs & Hc & Hk).
exact (conj Hw (conj Hs (conj Hc Hk))).
Qed.

(* a call's consumer window inside the text's (PRH_Base.prh_cons_from_sub): the events from position j, k' of them *)
Lemma crs_cons_sub : forall CTX0 C j k', (j + k' <= length (crs_evs C))%nat -> crs_pre CTX0 C ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C + j) k'.
Proof.
intros CTX0 C j k' Hk H. apply (prh_cons_from_sub _ _ _ _ (length (crs_evs C)) j k' Hk).
exact (proj2 (proj2 (proj2 (crs_pre_k1 CTX0 C H)))).
Qed.

(* the model's write makes at least one allocation (PRW_CrsModel.crs_wN_pos at PresetReqAt's wcaps) *)
Lemma crs_wcalls_pos : forall t p, (1 <= PresetReqAt.wcalls t p)%nat.
Proof. intros t p. unfold PresetReqAt.wcalls, PresetReqAt.wcaps. exact (crs_wN_pos t p). Qed.

Lemma crs_sw_S : forall x t p rest, PresetReqAt.starved_write x t p rest =
  PresetReqAt.w_evs t p ++ PresetReqAt.w_free t p ++
  PresetReqAt.w_starved t p (PresetReqAt.pick x (PresetReqAt.wcalls t p)) ++ rest.
Proof.
intros x t p rest. pose proof (crs_wcalls_pos t p) as H. unfold PresetReqAt.starved_write.
destruct (PresetReqAt.wcalls t p) as [|n] eqn:E; [lia | reflexivity].
Qed.

(* the whole list at the two ends: doc = 0 ends after the reading (W1's prefix), a tree after the compact
   injected write (X3's prefix and that write's events) *)
Lemma crs_evs_doc0 : forall C, c_doc C = 0 -> crs_evs C = crs_evs_at_W1 C.
Proof.
intros C H. unfold crs_evs, ck_crcs_evs, crs_evs_at_W1, crs_ev_sp.
rewrite (proj2 (Z.eqb_eq (c_doc C) 0) H). cbv iota. rewrite app_nil_r. reflexivity.
Qed.
Lemma crs_evs_doc : forall C, c_doc C <> 0 -> crs_evs C = crs_evs_at_X3 C ++ crs_ev_ws C false.
Proof.
intros C H. unfold crs_evs, ck_crcs_evs.
rewrite (proj2 (Z.eqb_neq (c_doc C) 0) H). cbv iota.
unfold PresetReqAt.starved_writes. rewrite !crs_sw_S, app_nil_r.
unfold crs_evs_at_X3, crs_evs_at_H3, crs_evs_at_Z, crs_evs_at_X2, crs_evs_at_H2, crs_evs_at_W1, crs_ev_sp,
  crs_ev_w, crs_ev_wf, crs_ev_ws.
repeat rewrite <- app_assoc. reflexivity.
Qed.

(* a split of the list gives the second part at the position after the first (PRH_Base.prh_run_at_app_iff) *)
Lemma crs_run_split : forall C e1 e2, crs_evs C = e1 ++ e2 ->
  prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) (crs_evs C) ->
  prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) e1 /\
  prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C + length e1)%nat e2.
Proof.
intros C e1 e2 E H. rewrite E in H. exact (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H).
Qed.

(* THE FREE SITES' EVENTS (replaces CrsEvsAp.v's interim premise crs_room_evs, blob d53ac0521f0c): with a tree, the
   run's event at W1's fuzz_free (the whole pretty text, 0x8234c) and at Z's fuzz_free (the whole compact text,
   0x82530) is the HFr of that text's last capacity plus the head, at the EXACT position the boundary's prefix and the
   write's w_evs name. tfuzz_free_specX's p <> 0 arm takes it as its one-event prh_run_at premise (PRH_FnAlloc.v:396; n + cf_head = that request).
   F's fuzz_free (s7) needs none: s7 = NULL when nothing was refused (crs_from_F). *)
Lemma crs_room_evs_of_run : forall C, c_doc C <> 0 ->
  prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C) (crs_evs C) ->
  nth_error (PresetRun.hruns ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C))
    (c_rp_i C + length (crs_evs_at_W1 C ++ crs_ev_w C true))%nat =
    Some (PresetReqAt.HFr (last (PresetReqAt.wcaps (c_t C) true) 0 + PresetReqAt.HEAD)) /\
  nth_error (PresetRun.hruns ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C))
    (c_rp_i C + length (crs_evs_at_Z C ++ crs_ev_w C false))%nat =
    Some (PresetReqAt.HFr (last (PresetReqAt.wcaps (c_t C) false) 0 + PresetReqAt.HEAD)).
Proof.
intros C Hd H. pose proof (crs_evs_doc C Hd) as E. split.
- assert (E1 : crs_evs C = (crs_evs_at_W1 C ++ crs_ev_w C true) ++ crs_ev_wf C true ++
                 (crs_ev_ws C true ++ crs_ev_w C false ++ crs_ev_wf C false ++ crs_ev_ws C false)).
  { rewrite E. unfold crs_evs_at_X3, crs_evs_at_H3, crs_evs_at_Z, crs_evs_at_X2, crs_evs_at_H2.
    repeat rewrite <- app_assoc. reflexivity. }
  destruct (crs_run_split C _ _ E1 H) as [_ H2].
  apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H2 as [H3 _].
  exact (proj1 (prh_run_at_one _ _ _ _
    (PresetReqAt.HFr (last (PresetReqAt.wcaps (c_t C) true) 0 + PresetReqAt.HEAD))) H3).
- assert (E2 : crs_evs C = (crs_evs_at_Z C ++ crs_ev_w C false) ++ crs_ev_wf C false ++ crs_ev_ws C false).
  { rewrite E. unfold crs_evs_at_X3, crs_evs_at_H3. repeat rewrite <- app_assoc. reflexivity. }
  destruct (crs_run_split C _ _ E2 H) as [_ H2].
  apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H2 as [H3 _].
  exact (proj1 (prh_run_at_one _ _ _ _
    (PresetReqAt.HFr (last (PresetReqAt.wcaps (c_t C) false) 0 + PresetReqAt.HEAD))) H3).
Qed.

(* ---- THE WRITER'S EXACT ADVANCE, by citation: tpj_write_specX (PRH_FnWriter.v:1142-1223) states prh_granted
   (DEAD-PJWRITE, :1193-1198) and its advance under it; PRH_Supply.v's prhWriter_pjw_evs_granted, prhWriter_pjw_evs_w_evs
   and prhWriter_pjw_evs_w_starved then name the events as the model's w_evs / w_starved, whose counts and pick are
   PjWriteHyp's and ck_pick's by the two bridges below. ---- *)

Lemma crs_wcalls_bridge : forall t p, PjWriteHyp.wcalls t p = Z.of_nat (PresetReqAt.wcalls t p).
Proof. intros t p. reflexivity. Qed.

Lemma crs_djb2_pick_h : forall x h, ck_djb2 h x = fold_left (fun h b => (h * 33 + b) mod 2 ^ 64) x h.
Proof.
intros x. induction x as [|c r IH]; intros h; cbn [ck_djb2 fold_left]; [reflexivity|].
rewrite IH. replace (33 * h) with (h * 33) by lia. reflexivity.
Qed.

Lemma crs_pick_bridge : forall x n, (0 < n)%nat -> ck_pick x (Z.of_nat n) = Z.of_nat (PresetReqAt.pick x n).
Proof.
intros x n Hn. destruct n as [|n']; [lia|].
unfold ck_pick, PresetReqAt.pick.
rewrite (proj2 (Z.eqb_neq (Z.of_nat (S n')) 0) ltac:(lia)). cbv iota.
unfold PresetReqAt.pick_h. rewrite <- crs_djb2_pick_h.
rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.

(* THE CHECK THAT crs_pre / crs_post ARE THE TEXT: an entry proof of crs_post for every C gives the text. crs_post
   is the text's budgeted post (fpostFbm (wbudget [] (prh_wk F_check_reject_clean_starved))), at the re-hiding
   relation as the text's conclusion; the entry context's journal depot is the entry's own, no budget spent. The
   text's premises are taken by shape (intros, then assumption per conjunct), so an added premise needs no edit here *)
Lemma crs_spec : forall CTX0,
  (forall C, crs_pre CTX0 C ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (c_W C)
       (cfg_at SEGS (SIGMA AS_check_reject_clean_starved) (c_regs C) (c_mem C) (c_md C)) (crs_post C)) ->
  tcheck_reject_clean_starved_specX (fx := fx) (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK CTX0.
Proof.
intros CTX0 HC. unfold tcheck_reject_clean_starved_specX.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most.
cbv zeta.
intros.
pose proof (HC (mkCrsC ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most
                  rp_x rp_os rp_i rp_H0 rp_hist 0 (st_depot S) [])) as HS.
assert (Hpre : crs_pre CTX0 (mkCrsC ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most
                  rp_x rp_os rp_i rp_H0 rp_hist 0 (st_depot S) [])).
{ unfold crs_pre, cSize, crs_evs. cbn [c_ly c_S c_Hp c_W c_regs c_mem c_md c_ch c_data c_tb c_took c_doc c_t c_D
    c_Lam c_peak c_cnt c_ran c_most c_rp_x c_rp_os c_rp_i c_rp_H0 c_rp_hist].
  repeat (split; [assumption|]). assumption. }
exact (HS Hpre).
Qed.

End f.
End d.

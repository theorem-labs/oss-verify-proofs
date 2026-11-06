(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1k.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN1k.v, with its module paths and module names changed; 305 of its 371 lines of code are new or changed and 439 lines of the source are left out. *)
(* fuzz_preset, file Crt102ImgB: the B' IMAGE FACTS of check_round_trip on the
   harness-fix #102 pins, section 6 of lib/A/Prog/Crt102Img.v: what the B listing and prh_img_B decide, and Section b
   over {PA : PAImg B_prog_listing} with the hypotheses HB_base / HB_entry / HB_segs / HB_relro / HB_hi (each closed
   at PI_prog_B by lib/B/Prog/CrtImgB102.v), and crt_offs_AB.

   MOVED, NOT WRITTEN: everything below CRT_STAMP_OFF_B is lib/A/Prog/Crt102Img.v lines 693-1082 (blob 64be5eda3b56 at
   commit 1cbd49de8e51) byte for byte, except the bodies of CRT_MOD_AT_B / CRT_STAMP_B, which read the B' twins
   CRT_MOD_AT_OFF_B / CRT_STAMP_OFF_B where they read Crt102Img.v's CRT_MOD_AT_OFF / CRT_STAMP_OFF. It was split out so
   that no A-tree file Requires lib.B (the shipping pool's shadow audit of the push head ab9f645e60d6; the unit owner's
   06:40Z ruling: split, no allow rows). The two twins follow the file's own pattern, a _B twin for every B' offset
   also where its value equals A's (CRT_E_OFF_B = CRT_E_OFF = 0); without them the moved text read two asan address
   constants of Crt102Img.v (shadow audit REF; the unit owner's 08:24Z ruling: B' twins read off the B listing).
   Crt102Img.v keeps sections 0-5 (the image-free checkers, the capacity premise, image A'), and the moved text reads
   them from it: csplit, res_pair, segf, str_at / str_at_sound, pa_res_add / pa_res_ld, opimm_at / load_at,
   CRT_MOD_AT_S / CRT_STAMP_S, and the A' offsets crt_offs_AB compares. The Requires are Crt102Img.v's own, in its
   order, less the A'-only modules (lib/A Img0 / Listing_prog / PAImg_prog / PRH_Img / PRH_FnCheck, YG05, YGcallScf,
   which the moved text does not read), then Crt102Img itself last, so each name in the moved text resolves as it did
   there.
   NUMERALS: CRT_MOD_AT_OFF_B 0x110c0 / CRT_STAMP_OFF_B 0x11380 are DERIVED (the B listing's PAddHi payloads, below).
   - rule 24: as Crt102Img.v (no function proved); nothing here is new text but the two twins.
   - build route pins102: the internal file zfb-targets.85055e6079bccb28.sh, FACTS 8f3e7e1a07f1, PAU the #102 pin set
     (pau-preset-102). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YP0m YP02 YP0b YPsym YImgTop YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Img.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

(* ---- the B' twins of Crt102Img.v's CRT_MOD_AT_OFF / CRT_STAMP_OFF: the two strings' offsets from pa_val (A_OBJ 2),
   read off the B listing. They are its PAddHi payloads at the five string sites, and no other line of it carries
   them: lib/B/Listing_prog.v:1274 (STAMP1, 0x11380), :1283 (MODAT1, 0x110c0), :1440 (MODAT2, 0x110c0), :1596 (MODAT3,
   0x110c0), :1633 (STAMP2, 0x11380); crt_str_lst_B below checks all five. the internal file crt.B.s agrees: its five auipc / addi pairs
   compute 0x21380 / 0x210c0 / 0x210c0 / 0x210c0 / 0x21380, and B_prog_val (A_OBJ 2) is 0x10000 (B/PAImg_prog.v:193). *)
Definition CRT_MOD_AT_OFF_B : Z := 0x110c0.
Definition CRT_STAMP_OFF_B : Z := 0x11380.

(* ======================================================================================================== *)
(* 6. image B': everything the B listing and prh_img_B decide, PA-free                                       *)

(* the function's slot in B_prog_listing: (0x82828 - B_prog_base) / 4 (the internal file crt.B.s line 1; B/Listing_prog.v:12) *)
Definition CRT_SLOT_B : nat := 1111.
Definition CRT_PC_B : Z := 4 * Z.of_nat CRT_SLOT_B.
Definition CRT_E_OFF_B : Z := 0x0.  (* 0x82828: prologue: addi sp,sp,-0xe0; 13 saves; s0 = sp0; andi sp,sp,-0x20; GOT loads; flag test *)
Definition CRT_P_OFF_B : Z := 0x70. (* 0x82898: __asan_stack_malloc_3's return: mv s3, a0 *)
Definition CRT_H_OFF_B : Z := 0xa0. (* 0x828c8: sd s3,0x70(s1): the frame F spilled (B' keeps F in s3, not s11); frame header and the 40 shadow bytes *)
Definition CRT_M_OFF_B : Z := 0x194. (* 0x829bc: __asan_memset's return: a0 = doc, a1 = 0, a2 = &copy *)
Definition CRT_R1_OFF_B : Z := 0x1a4. (* 0x829cc: rtt1's return: beqz a0 (arm C1 otherwise) *)
Definition CRT_R2_OFF_B : Z := 0x1c4. (* 0x829ec: rtt2's return: bnez a0 -> J (arm C2) *)
Definition CRT_T_OFF_B : Z := 0x1c8. (* 0x829f0: doc shadow check, doc->type == 6 test (arm C3 otherwise) *)
Definition CRT_U_OFF_B : Z := 0x1ec. (* 0x82a14: unpoison of back / v, &doc->n, doc->n *)
Definition CRT_G_OFF_B : Z := 0x25c. (* 0x82a84: pj_string's return *)
Definition CRT_C3_OFF_B : Z := 0x268. (* 0x82a90: arm C3: mv s5, zero (B' return flag in s5, not s6), j J *)
Definition CRT_K_OFF_B : Z := 0x284. (* 0x82aac: pj_set's return: s8 = seqz a0 *)
Definition CRT_O1_OFF_B : Z := 0x288. (* 0x82ab0: the flag tests g_own_ran_out / fuzz_alloc_ran_out (arm C4a), beqz s8 -> AB *)
Definition CRT_W_OFF_B : Z := 0x2bc. (* 0x82ae4: pj_write's return: s8 = saved *)
Definition CRT_N_OFF_B : Z := 0x2ec. (* 0x82b14: parse_noting's return: snez s5, a0 (B' flag in s5, not s6) *)
Definition CRT_O2_OFF_B : Z := 0x2f0. (* 0x82b18: the flag tests after the read-back; beqz -> L0 *)
Definition CRT_FF_OFF_B : Z := 0x300. (* 0x82b28: arm C4c: fuzz_free (saved), addi s5, zero, 1 at +0x308 (B' flag in s5) *)
Definition CRT_X_OFF_B : Z := 0x30c. (* 0x82b34: the shared re-poison of back / v *)
Definition CRT_J_OFF_B : Z := 0x348. (* 0x82b70: the join: a0 = &copy, jal pj_free *)
Definition CRT_Z_OFF_B : Z := 0x350. (* 0x82b78: pj_free's return: poison of copy, the retired magic, beqz s7 at +0x378 (B' frame-call result in s7, not s3) *)
Definition CRT_Z5_OFF_B : Z := 0x388. (* 0x82bb0: __asan_set_shadow_f5's return: the flag store ld a0,0x1f8(s7); sb zero,0(a0) (B' frame-call result in s7, not s3) *)
Definition CRT_ZS_OFF_B : Z := 0x394. (* 0x82bbc: the stack-path retire (beqz s7 taken): the 40 shadow bytes zeroed *)
Definition CRT_Q_OFF_B : Z := 0x434. (* 0x82c5c: mv a0, s5 (B' flag in s5, not s6), the 13 restores *)
Definition CRT_RET_OFF_B : Z := 0x474. (* 0x82c9c: ret *)
Definition CRT_L0_OFF_B : Z := 0x478. (* 0x82ca0: sd s8,0(s1), bnez s5 at +0x47c -> AB (B' flag in s5, not s6); the at-search set-up *)
Definition CRT_L1_OFF_B : Z := 0x4f8. (* 0x82d20: the at-search loop head (strcmp (doc->keys[i], MOD_AT)) *)
Definition CRT_L2_OFF_B : Z := 0x56c. (* 0x82d94: back.n test, the member loop set-up *)
Definition CRT_L3_OFF_B : Z := 0x5b4. (* 0x82ddc: the member loop head (strcmp keys, same kids) *)
Definition CRT_C_OFF_B : Z := 0x6f8. (* 0x82f20: the final checks (MOD_AT key, type 4, STAMP) *)
Definition CRT_AB_OFF_B : Z := 0x824. (* 0x8304c: the abort tail: jal __asan_handle_no_return; jal abort *)
Definition CRT_UB_OFF_B : Z := 0x810. (* 0x83038: the UBSan trap (unimp) every B-only overflow / alignment check branches to *)
Definition CRT_SM3_CALL_B : Z := 0x6c. (* 0x82894: jal __asan_stack_malloc_3 *)
Definition CRT_MEMSET_CALL_B : Z := 0x190. (* 0x829b8: jal __asan_memset *)
Definition CRT_RTT1_CALL_B : Z := 0x1a0. (* 0x829c8: jal round_trip_text *)
Definition CRT_RTT2_CALL_B : Z := 0x1c0. (* 0x829e8: jal round_trip_text *)
Definition CRT_PJSTR_CALL_B : Z := 0x258. (* 0x82a80: jal pj_string *)
Definition CRT_PJSET_CALL_B : Z := 0x280. (* 0x82aa8: jal pj_set *)
Definition CRT_RO1_CALL_B : Z := 0x298. (* 0x82ac0: jal fuzz_alloc_ran_out *)
Definition CRT_PJW_CALL_B : Z := 0x2b8. (* 0x82ae0: jal pj_write *)
Definition CRT_RO2_CALL_B : Z := 0x2cc. (* 0x82af4: jal fuzz_alloc_ran_out *)
Definition CRT_STRLEN_CALL_B : Z := 0x2d8. (* 0x82b00: jal __wrap_strlen *)
Definition CRT_PN_CALL_B : Z := 0x2e8. (* 0x82b10: jal parse_noting *)
Definition CRT_RO3_CALL_B : Z := 0x2f8. (* 0x82b20: jal fuzz_alloc_ran_out *)
Definition CRT_FF1_CALL_B : Z := 0x304. (* 0x82b2c: jal fuzz_free *)
Definition CRT_PJF1_CALL_B : Z := 0x34c. (* 0x82b74: jal pj_free *)
Definition CRT_SSF5_CALL_B : Z := 0x384. (* 0x82bac: jal __asan_set_shadow_f5 *)
Definition CRT_CMP1_CALL_B : Z := 0x53c. (* 0x82d64: jal __wrap_strcmp *)
Definition CRT_CMP2_CALL_B : Z := 0x648. (* 0x82e70: jal __wrap_strcmp *)
Definition CRT_SAME_CALL_B : Z := 0x6cc. (* 0x82ef4: jal same *)
Definition CRT_CMP3_CALL_B : Z := 0x75c. (* 0x82f84: jal __wrap_strcmp *)
Definition CRT_CMP4_CALL_B : Z := 0x7f0. (* 0x83018: jal __wrap_strcmp *)
Definition CRT_FF2_CALL_B : Z := 0x7fc. (* 0x83024: jal fuzz_free *)
Definition CRT_PJF2_CALL_B : Z := 0x804. (* 0x8302c: jal pj_free *)
Definition CRT_HNR_CALL_B : Z := 0x824. (* 0x8304c: jal __asan_handle_no_return *)
Definition CRT_ABORT_CALL_B : Z := 0x828. (* 0x83050: jal abort *)
Definition CRT_GOT_SHB_HI_B : Z := 0x48.   Definition CRT_GOT_SHB_LO_B : Z := 0x54.
Definition CRT_GOT_UAR_HI_B : Z := 0x4c.   Definition CRT_GOT_UAR_LO_B : Z := 0x50.
Definition CRT_FLAG_LW_B : Z := 0x58.      Definition CRT_SHB_LD_B : Z := 0x5c.
Definition CRT_STAMP1_HI_B : Z := 0x24c.   Definition CRT_STAMP1_LO_B : Z := 0x250.
Definition CRT_MODAT1_HI_B : Z := 0x270.   Definition CRT_MODAT1_LO_B : Z := 0x274.
Definition CRT_MODAT2_HI_B : Z := 0x4cc.   Definition CRT_MODAT2_LO_B : Z := 0x4e8.
Definition CRT_MODAT3_HI_B : Z := 0x754.   Definition CRT_MODAT3_LO_B : Z := 0x758.
Definition CRT_STAMP2_HI_B : Z := 0x7e8.   Definition CRT_STAMP2_LO_B : Z := 0x7ec.
Definition CRT_ERR_OFFS_B : list Z :=
  [0x820; 0x838; 0x83c; 0x840; 0x848; 0x850; 0x858; 0x860; 0x868; 0x870; 0x874; 0x878; 0x87c].

(* the frame header's pc word is the listing's A_TEXT + CRT_PC_B: the B listing itself puts the function at this slot *)
Lemma crt_pc_hdr_B : plookup_list asym B_prog_listing (CRT_PC_B + 0xc4) =
  Some (PAddHi (12%bv : bv 5) (12%bv : bv 5) 32 A_TEXT CRT_PC_B).
Proof. vm_compute. reflexivity. Qed.

Lemma crt_cut_E_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_E_OFF_B) = Some (PW 0xf2010113).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_P_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_P_OFF_B) = Some (PW 0x50b93).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_H_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_H_OFF_B) = Some (PW 0x734b823).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_M_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_M_OFF_B) = Some (PW 0xb0513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_R1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_R1_OFF_B) = Some (PW 0x50663).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_R2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_R2_OFF_B) = Some (PW 0x18051263).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_T_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_T_OFF_B) = Some (PW 0x7b7513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_U_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_U_OFF_B) = Some (PW 0x90223).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_G_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_G_OFF_B) = Some (PW 0x50a63).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_C3_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_C3_OFF_B) = Some (PW 0xa93).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_K_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_K_OFF_B) = Some (PW 0x153c13).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_O1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_O1_OFF_B) = Some (PHi (26%bv : bv 5) 35).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_W_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_W_OFF_B) = Some (PW 0x50c13).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_N_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_N_OFF_B) = Some (PW 0xa03ab3).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_O2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_O2_OFF_B) = Some (PW 0x2d0d4503).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_FF_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_FF_OFF_B) = Some (PW 0xc0513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_X_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_X_OFF_B) = Some (PW 0xff800513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_J_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_J_OFF_B) = Some (PW 0xa0513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_Z_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_Z_OFF_B) = Some (PW 0x1990e23).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_Z5_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_Z5_OFF_B) = Some (PW 0x1f8bb503).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_ZS_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_ZS_OFF_B) = Some (PW 0x90223).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_Q_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_Q_OFF_B) = Some (PW 0xa8513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_RET_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_RET_OFF_B) = Some (PW 0x8067).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_L0_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_L0_OFF_B) = Some (PW 0x184b023).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_L1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_L1_OFF_B) = Some (PW 0x1d3513).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_L2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_L2_OFF_B) = Some (PW 0x4b4b023).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_L3_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_L3_OFF_B) = Some (PW 0x384b503).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_C_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_C_OFF_B) = Some (PW 0x384b503).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_AB_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_AB_OFF_B) = Some (PCall AS___asan_handle_no_return (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_UB_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_UB_OFF_B) = Some (PW 0xc0001073).
Proof. vm_compute. reflexivity. Qed.

Lemma crt_call_SM3_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_SM3_CALL_B) = Some (PCall AS___asan_stack_malloc_3 (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_MEMSET_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_MEMSET_CALL_B) = Some (PCall AS___asan_memset (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RTT1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_RTT1_CALL_B) = Some (PCall AS_round_trip_text (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RTT2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_RTT2_CALL_B) = Some (PCall AS_round_trip_text (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJSTR_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_PJSTR_CALL_B) = Some (PCall AS_pj_string (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJSET_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_PJSET_CALL_B) = Some (PCall AS_pj_set (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RO1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_RO1_CALL_B) = Some (PCall AS_fuzz_alloc_ran_out (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJW_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_PJW_CALL_B) = Some (PCall AS_pj_write (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RO2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_RO2_CALL_B) = Some (PCall AS_fuzz_alloc_ran_out (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_STRLEN_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_STRLEN_CALL_B) = Some (PCall AS___wrap_strlen (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PN_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_PN_CALL_B) = Some (PCall AS_parse_noting (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RO3_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_RO3_CALL_B) = Some (PCall AS_fuzz_alloc_ran_out (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_FF1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_FF1_CALL_B) = Some (PCall AS_fuzz_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJF1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_PJF1_CALL_B) = Some (PCall AS_pj_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_SSF5_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_SSF5_CALL_B) = Some (PCall AS___asan_set_shadow_f5 (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP1_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_CMP1_CALL_B) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_CMP2_CALL_B) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_SAME_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_SAME_CALL_B) = Some (PCall AS_same (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP3_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_CMP3_CALL_B) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP4_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_CMP4_CALL_B) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_FF2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_FF2_CALL_B) = Some (PCall AS_fuzz_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJF2_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_PJF2_CALL_B) = Some (PCall AS_pj_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_HNR_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_HNR_CALL_B) = Some (PCall AS___asan_handle_no_return (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_ABORT_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_ABORT_CALL_B) = Some (PCall AS_abort (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.

#[local] Notation ATB o := (B_prog_base + (CRT_PC_B + o)).
Lemma crt_img_B :
  @pi_call_rets prh_img_B F_check_round_trip F_round_trip_text = [ATB CRT_R1_OFF_B; ATB CRT_R2_OFF_B] /\
  @pi_call_rets prh_img_B F_check_round_trip F_pj_string = [ATB CRT_G_OFF_B] /\
  @pi_call_rets prh_img_B F_check_round_trip F_pj_set = [ATB CRT_K_OFF_B] /\
  @pi_call_rets prh_img_B F_check_round_trip F_pj_write = [ATB CRT_W_OFF_B] /\
  @pi_call_rets prh_img_B F_check_round_trip F_parse_noting = [ATB CRT_N_OFF_B] /\
  @pi_call_rets prh_img_B F_check_round_trip F_pj_free = [ATB CRT_Z_OFF_B; ATB (CRT_PJF2_CALL_B + 4)] /\
  @pi_call_rets prh_img_B F_check_round_trip F_fuzz_free = [ATB (CRT_FF1_CALL_B + 4); ATB (CRT_FF2_CALL_B + 4)] /\
  @pi_call_rets prh_img_B F_check_round_trip F_fuzz_alloc_ran_out =
    [ATB (CRT_RO1_CALL_B + 4); ATB (CRT_RO2_CALL_B + 4); ATB (CRT_RO3_CALL_B + 4)] /\
  @pi_call_rets prh_img_B F_check_round_trip F_same = [ATB (CRT_SAME_CALL_B + 4)] /\
  @pi_ret_sites prh_img_B F_check_round_trip RT_fuzz_free = [ATB (CRT_FF1_CALL_B + 4); ATB (CRT_FF2_CALL_B + 4)] /\
  @pi_abort prh_img_B F_check_round_trip = ATB CRT_AB_OFF_B /\
  @pi_err_sites prh_img_B F_check_round_trip = map (fun o => ATB o) CRT_ERR_OFFS_B.
Proof. csplit; vm_compute; reflexivity. Qed.

Lemma crt_frame_B :
  opimm_at B_prog_listing CRT_PC_B = Some (ALU_ADD, 2, 2, - Crt102Glue.CRT_FRAME) /\
  opimm_at B_prog_listing (CRT_PC_B + 0x3c) = Some (ALU_ADD, 8, 2, Crt102Glue.CRT_FRAME) /\
  opimm_at B_prog_listing (CRT_PC_B + 0x40) = Some (ALU_AND, 2, 2, - Crt102Glue.CRT_ALIGN) /\
  opimm_at B_prog_listing (CRT_PC_B + 0x68) = Some (ALU_ADD, 10, 0, Crt102Glue.CRT_REQ) /\
  @pi_frame prh_img_B F_check_round_trip = Crt102Glue.CRT_FRAME + (Crt102Glue.CRT_ALIGN - 16).
Proof. csplit; vm_compute; reflexivity. Qed.
(* B' keeps the shadow base in s11 (27, not s10), doc in s6 (22, not s5), the frame call's result in s7 (23, not s3),
   F in s3 (19, from s7; not s11) and -8 in s9 (25, not s7) *)
Lemma crt_regs_B :
  load_at B_prog_listing (CRT_PC_B + CRT_FLAG_LW_B) = Some (SZ4, true, 12, 12, 0) /\
  load_at B_prog_listing (CRT_PC_B + CRT_SHB_LD_B) = Some (SZ8, true, 27, 11, 0) /\
  opimm_at B_prog_listing (CRT_PC_B + 0x60) = Some (ALU_ADD, 22, 10, 0) /\
  opimm_at B_prog_listing (CRT_PC_B + CRT_P_OFF_B) = Some (ALU_ADD, 23, 10, 0) /\
  opimm_at B_prog_listing (CRT_PC_B + 0x7c) = Some (ALU_ADD, 19, 23, 0) /\
  opimm_at B_prog_listing (CRT_PC_B + 0xb8) = Some (ALU_ADD, 25, 0, -8).
Proof. csplit; vm_compute; reflexivity. Qed.

Lemma crt_stk_B :
  ESTACK + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  STK_RT_ECALL + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  STK_RT_STR + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_round_trip_text prh_img_B + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_pj_string prh_img_B + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_pj_set prh_img_B DOC_D + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_pj_write prh_img_B DOC_D + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_parse_noting prh_img_B + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_pj_free prh_img_B DOC_D + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_fuzz_free prh_img_B + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_fuzz_alloc_ran_out prh_img_B + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B /\
  @STK_same prh_img_B DOC_D + @pi_frame prh_img_B F_check_round_trip <= @STK_check_round_trip prh_img_B.
Proof. csplit; vm_compute; discriminate. Qed.
Lemma crt_stk_nonneg_B :
  0 <= @pi_frame prh_img_B F_check_round_trip /\
  0 <= @STK_round_trip_text prh_img_B /\ 0 <= @STK_pj_string prh_img_B /\ 0 <= @STK_pj_set prh_img_B DOC_D /\
  0 <= @STK_pj_write prh_img_B DOC_D /\ 0 <= @STK_parse_noting prh_img_B /\ 0 <= @STK_pj_free prh_img_B DOC_D /\
  0 <= @STK_fuzz_free prh_img_B /\ 0 <= @STK_fuzz_alloc_ran_out prh_img_B /\ 0 <= @STK_same prh_img_B DOC_D.
Proof. csplit; vm_compute; discriminate. Qed.

(* the string sites: the B listing's entries, and the B image's own words (fetch_word over lib/B/Img0.v's rsegs)
   resolve to the two strings' bytes *)
Lemma crt_str_lst_B :
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_STAMP1_HI_B) = Some (PHi (10%bv : bv 5) 33) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_STAMP1_LO_B) = Some (PAddHi (11%bv : bv 5) (10%bv : bv 5) 33 (A_OBJ 2) 0x11380) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_MODAT1_HI_B) = Some (PHi (10%bv : bv 5) 34) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_MODAT1_LO_B) = Some (PAddHi (11%bv : bv 5) (10%bv : bv 5) 34 (A_OBJ 2) 0x110c0) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_MODAT2_HI_B) = Some (PHi (10%bv : bv 5) 36) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_MODAT2_LO_B) = Some (PAddHi (10%bv : bv 5) (10%bv : bv 5) 36 (A_OBJ 2) 0x110c0) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_MODAT3_HI_B) = Some (PHi (11%bv : bv 5) 37) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_MODAT3_LO_B) = Some (PAddHi (11%bv : bv 5) (11%bv : bv 5) 37 (A_OBJ 2) 0x110c0) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_STAMP2_HI_B) = Some (PHi (11%bv : bv 5) 38) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_STAMP2_LO_B) = Some (PAddHi (11%bv : bv 5) (11%bv : bv 5) 38 (A_OBJ 2) 0x11380).
Proof. csplit; vm_compute; reflexivity. Qed.
Definition str_res_b (segs : list Segment) (p1 p2 : Z) (s : list Z) : bool :=
  match res_pair (segf segs) p1 p2 with Some p => str_at segs p s | None => false end.
Lemma crt_str_raw_B :
  str_res_b B.Img0.rsegs (ATB CRT_STAMP1_HI_B) (ATB CRT_STAMP1_LO_B) CRT_STAMP_S = true /\
  str_res_b B.Img0.rsegs (ATB CRT_MODAT1_HI_B) (ATB CRT_MODAT1_LO_B) CRT_MOD_AT_S = true /\
  str_res_b B.Img0.rsegs (ATB CRT_MODAT2_HI_B) (ATB CRT_MODAT2_LO_B) CRT_MOD_AT_S = true /\
  str_res_b B.Img0.rsegs (ATB CRT_MODAT3_HI_B) (ATB CRT_MODAT3_LO_B) CRT_MOD_AT_S = true /\
  str_res_b B.Img0.rsegs (ATB CRT_STAMP2_HI_B) (ATB CRT_STAMP2_LO_B) CRT_STAMP_S = true.
Proof. csplit; vm_compute; reflexivity. Qed.
Lemma crt_got_lst_B :
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_GOT_SHB_HI_B) = Some (PHi (11%bv : bv 5) 29) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_GOT_SHB_LO_B) =
    Some (PLdHi (11%bv : bv 5) (11%bv : bv 5) 29 (A_OBJ 0) 0x0 SZ8 true) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_GOT_UAR_HI_B) = Some (PHi (12%bv : bv 5) 30) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_GOT_UAR_LO_B) =
    Some (PLdHi (12%bv : bv 5) (12%bv : bv 5) 30 (A_OBJ 1) 0x0 SZ8 true).
Proof. csplit; vm_compute; reflexivity. Qed.
(* alloc.c's statics at prh_img_B: image bytes of B's segments, and in no read-only segment (relro is HB_relro's) *)
Lemma pst_img_b_B0 : pst_allb (in_img_b B.Img0.rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pst_ro_seg_b_B0 : pst_allb (fun a => negb (in_ro_b B.Img0.rsegs 0 0 a)) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* WHICH OFFSETS AGREE ON A' AND B' (the brief's claim for round_trip_text, checked for check_round_trip): the cuts E,
   P, H, M, R1, R2, T and the jal sites +0x6c / +0x190 / +0x1a0 / +0x1c0, the GOT pairs, and the frame; every other
   cut and jal site differs (B' runs UBSan's alignment check at the start of T and pointer-overflow checks in the
   loops), the string sites too. *)
Lemma crt_offs_AB :
  CRT_E_OFF = CRT_E_OFF_B /\ CRT_P_OFF = CRT_P_OFF_B /\ CRT_H_OFF = CRT_H_OFF_B /\ CRT_M_OFF = CRT_M_OFF_B /\
  CRT_R1_OFF = CRT_R1_OFF_B /\ CRT_R2_OFF = CRT_R2_OFF_B /\ CRT_T_OFF = CRT_T_OFF_B /\
  CRT_SM3_CALL = CRT_SM3_CALL_B /\ CRT_MEMSET_CALL = CRT_MEMSET_CALL_B /\ CRT_RTT1_CALL = CRT_RTT1_CALL_B /\
  CRT_RTT2_CALL = CRT_RTT2_CALL_B /\
  CRT_U_OFF <> CRT_U_OFF_B /\ CRT_G_OFF <> CRT_G_OFF_B /\ CRT_C3_OFF <> CRT_C3_OFF_B /\ CRT_K_OFF <> CRT_K_OFF_B /\
  CRT_O1_OFF <> CRT_O1_OFF_B /\ CRT_W_OFF <> CRT_W_OFF_B /\ CRT_N_OFF <> CRT_N_OFF_B /\ CRT_O2_OFF <> CRT_O2_OFF_B /\
  CRT_FF_OFF <> CRT_FF_OFF_B /\ CRT_X_OFF <> CRT_X_OFF_B /\ CRT_J_OFF <> CRT_J_OFF_B /\ CRT_Z_OFF <> CRT_Z_OFF_B /\
  CRT_Z5_OFF <> CRT_Z5_OFF_B /\ CRT_ZS_OFF <> CRT_ZS_OFF_B /\ CRT_Q_OFF <> CRT_Q_OFF_B /\
  CRT_RET_OFF <> CRT_RET_OFF_B /\ CRT_L0_OFF <> CRT_L0_OFF_B /\ CRT_L1_OFF <> CRT_L1_OFF_B /\
  CRT_L2_OFF <> CRT_L2_OFF_B /\ CRT_L3_OFF <> CRT_L3_OFF_B /\ CRT_C_OFF <> CRT_C_OFF_B /\ CRT_AB_OFF <> CRT_AB_OFF_B /\
  CRT_PJSTR_CALL <> CRT_PJSTR_CALL_B /\ CRT_STAMP1_HI <> CRT_STAMP1_HI_B /\ CRT_MODAT1_HI <> CRT_MODAT1_HI_B.
Proof. csplit; vm_compute; first [reflexivity | discriminate]. Qed.

(* ---- B' at a PAImg instance of the B listing: the values only the instance carries are the hypotheses below,
   each with its B' value; at PI_prog_B each is vm_compute (HB_relro: S1ImgB.v's pst_ro_b_B) ---- *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation AT o := (BASE + (CRT_PC_B + o)).
(* B' value: pa_val A_TEXT = B_prog_val A_TEXT = B_prog_base (0x816cc), as A's PAImg_prog.v:381 / :404 *)
Hypothesis HB_base : BASE = B_prog_base.
(* B' value: pa_sigma AS_check_round_trip = B_prog_sigma AS_check_round_trip = 0x82828 (B/PAImg_prog.v:28; the internal file crt.B.s
   line 1) = B_prog_base + 0x115c; crt_pc_hdr_B is the listing's own word for it *)
Hypothesis HB_entry : SIGMA AS_check_round_trip = B_prog_base + CRT_PC_B.
(* B' value: pa_segs = rsegs of lib/B/Img0.v (images.AsanUbsan), as A's PAImg_prog.v:404 *)
Hypothesis HB_segs : SEGS = B.Img0.rsegs.
(* B' value: relro [0xa2240, 0xa4000) (B/PAImg_prog.v:162-163); prh_img_B's statics are 0x5ddd80 .. 0x5dde08,
   0xa6e00 and 0xa6e20, outside it *)
Hypothesis HB_relro : forall a, Exists (in_zr a) PST -> ~ (RLO <= a < RHI).
(* B' value: pa_hi = IMG_TOP_B = 0x601000 (B/PAImg_prog.v:407; lib/Reusable/YImgTop.v:23) *)
Hypothesis HB_hi : @pa_hi _ B_prog_listing PA <= 2 ^ 31.

Lemma crt_pc_B : BASE + CRT_PC_B = SIGMA AS_check_round_trip.
Proof. rewrite HB_base, HB_entry. reflexivity. Qed.
Lemma crt_cut_pc_B : forall off, BASE + (CRT_PC_B + off) = SIGMA AS_check_round_trip + off.
Proof. intros off. rewrite <- crt_pc_B. lia. Qed.
Lemma crt_at_B : forall off, AT off = ATB off.
Proof. intros off. rewrite HB_base. reflexivity. Qed.
Lemma crt_abort_B : @pi_abort prh_img_B F_check_round_trip = AT CRT_AB_OFF_B.
Proof. rewrite crt_at_B. vm_compute. reflexivity. Qed.

Definition CRT_MOD_AT_B : Z := VAL (A_OBJ 2) + CRT_MOD_AT_OFF_B.
Definition CRT_STAMP_B : Z := VAL (A_OBJ 2) + CRT_STAMP_OFF_B.
(* the instance's own instruction words at the five sites resolve to the two addresses (from pa_cert) *)
Lemma crt_str_res_B :
  res_pair (segf SEGS) (AT CRT_STAMP1_HI_B) (AT CRT_STAMP1_LO_B) = Some CRT_STAMP_B /\
  res_pair (segf SEGS) (AT CRT_MODAT1_HI_B) (AT CRT_MODAT1_LO_B) = Some CRT_MOD_AT_B /\
  res_pair (segf SEGS) (AT CRT_MODAT2_HI_B) (AT CRT_MODAT2_LO_B) = Some CRT_MOD_AT_B /\
  res_pair (segf SEGS) (AT CRT_MODAT3_HI_B) (AT CRT_MODAT3_LO_B) = Some CRT_MOD_AT_B /\
  res_pair (segf SEGS) (AT CRT_STAMP2_HI_B) (AT CRT_STAMP2_LO_B) = Some CRT_STAMP_B.
Proof.
destruct crt_str_lst_B as (S1 & T1 & S2 & T2 & S3 & T3 & S4 & T4 & S5 & T5).
unfold CRT_MOD_AT_B, CRT_STAMP_B.
split; [exact (pa_res_add _ _ _ _ _ _ _ S1 T1)|]. split; [exact (pa_res_add _ _ _ _ _ _ _ S2 T2)|].
split; [exact (pa_res_add _ _ _ _ _ _ _ S3 T3)|]. split; [exact (pa_res_add _ _ _ _ _ _ _ S4 T4)|].
exact (pa_res_add _ _ _ _ _ _ _ S5 T5).
Qed.
(* the bytes there *)
Lemma crt_str_rom_b_B :
  str_at SEGS CRT_MOD_AT_B CRT_MOD_AT_S = true /\
  str_at SEGS CRT_STAMP_B CRT_STAMP_S = true.
Proof.
destruct crt_str_res_B as (H1 & H2 & _).
destruct crt_str_raw_B as (R1 & R2 & _).
rewrite HB_segs, !crt_at_B in H1, H2. unfold str_res_b in R1, R2. rewrite H1 in R1. rewrite H2 in R2.
cbv beta iota in R1, R2. rewrite HB_segs. split; [exact R2 | exact R1].
Qed.
Lemma crt_str_rom_B :
  (forall j, (j < length CRT_MOD_AT_S)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (CRT_MOD_AT_B + Z.of_nat j))) =
     Some (nth j CRT_MOD_AT_S 0)) /\
  (forall j, (j < length CRT_STAMP_S)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (CRT_STAMP_B + Z.of_nat j))) =
     Some (nth j CRT_STAMP_S 0)).
Proof. split; apply str_at_sound; [exact (proj1 crt_str_rom_b_B) | exact (proj2 crt_str_rom_b_B)]. Qed.

(* the prologue's GOT words on B': A_OBJ 0 and A_OBJ 1 as on A' (from pa_cert) *)
Lemma crt_got_B :
  res_pair (segf SEGS) (AT CRT_GOT_SHB_HI_B) (AT CRT_GOT_SHB_LO_B) = Some (VAL (A_OBJ 0)) /\
  res_pair (segf SEGS) (AT CRT_GOT_UAR_HI_B) (AT CRT_GOT_UAR_LO_B) = Some (VAL (A_OBJ 1)).
Proof.
destruct crt_got_lst_B as (H1 & H2 & H3 & H4). split.
- rewrite <- (Z.add_0_r (VAL (A_OBJ 0))). exact (pa_res_ld _ _ _ _ _ _ _ _ _ H1 H2).
- rewrite <- (Z.add_0_r (VAL (A_OBJ 1))). exact (pa_res_ld _ _ _ _ _ _ _ _ _ H3 H4).
Qed.

(* the image facts a journal needs *)
Lemma crt_pst_img_B : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. intros a Ha. rewrite HB_segs. apply in_img_b_sound. exact (pst_allb_sound _ _ a pst_img_b_B0 Ha). Qed.
Lemma crt_pst_ro_B : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof.
intros a Ha [(s & Hs & Hw & Hr) | Hr].
- rewrite HB_segs in Hs. pose proof (pst_allb_sound _ _ a pst_ro_seg_b_B0 Ha) as H. cbv beta in H.
  rewrite (in_ro_b_complete B.Img0.rsegs 0 0 a (or_introl (ex_intro _ s (conj Hs (conj Hw Hr))))) in H.
  cbn [negb] in H. discriminate H.
- exact (HB_relro a Ha Hr).
Qed.
Lemma crt_pa_hi_B : @pa_hi _ B_prog_listing PA <= 2 ^ 31.
Proof. exact HB_hi. Qed.
End b.

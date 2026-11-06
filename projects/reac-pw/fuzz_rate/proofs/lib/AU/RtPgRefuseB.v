(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/RPgCheck.v at fb6520a9cda (its entry state, save-slot region, run / keep / leaf chain and write obligations, reused by Require) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_refuse_code 0x82e6c against lib/A/RPgCSpec.v's rl_refuse_code_specX on the concrete image lib/A/Img0.v rsegs, with its own code table (23 words from 0x82e6c), the a0 clause of lib/A/RPgCfgChanges.v's cfg_leaf and its cfg_branch split, and the .got-slot / shadow-offset-cell regions of proofs/libreac/fuzz_knock/lib/A/ACeh.v got_region / bcell_region at origin/ossv/recipes 6ebe35ba632 (with lib/A/APgRt.v's al_const / chunk_ok_val / val_mem_of_rdword proofs of them); new: the regions of the two shadow bytes of the table and of the table itself, and the split on a0 (r >= 2: one branch; r = 0, r = 1: a0 a literal). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgRefuse.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments; the contract is
   lib/A/RtPgCSpec.v's rt_refuse_code_specX, whose table premise is RtPgBase's rt_u64tab (5 entries) where role's are
   two val_mem cells and a 16-byte range_addressable; the `bgeu` bound is 4 (role 1), so the split on a0 is r >= 5
   (one branch) and r = 0 .. 4 (a0 a literal); the .got slot, the shadow offset cell, the table, its five shadow bytes
   and the literal of the r >= 5 path are rate's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgRefuse.v at b908b1be5a37 (its walk
   rt_refuse_code_A) for reac-pw/fuzz_rate's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan's loaded
   segments; the entry states, regions, code table (27 words) and the run / branch / keep / leaf plumbing are
   lib/AU/RtPgRefuse.v's and lib/AU/RtPgCheck.v's (image A's lib/A/RtPgRefuse.v and lib/A/RtPgCheck.v at image B),
   Required, not restated; the pcs are B's; B's code forms the table's address before it reads the shadow offset cell
   and has one more branch, the pointer-overflow trap 0x841e0, whose step is the one of
   proofs/reac-pw/fuzz_rate/lib/U/Prog/reac_rate_refuse_code.v at 09704c734de1 (reac_rate_refuse_code_holds, `not a3, a1;
   bltu a3, a2: not taken` on the literal a0 = 0 .. 4); the record hypotheses name B's .got slot 0x9c170 and shadow
   offset cell 0xa4f38. *)
(* reac_rate_refuse_code, 0x841b4, 108 bytes, 27 words (fuzz_rate.asan-ubsan, unstripped sha256
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1; the pinned
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14 has the same loaded bytes):
     0x841b4 addi sp,sp,-0x10; 0x841b8 sd ra,8(sp); 0x841bc addi a1,zero,4; 0x841c0 bgeu a1,a0,0x841d0;
     0x841c4 auipc a0,0xfff9d; 0x841c8 addi a0,a0,0x43c (a0 = 0x21600); 0x841cc j 0x8420c;
     0x841d0 slli a2,a0,3; 0x841d4 auipc a1,0x18; 0x841d8 addi a1,a1,-0x254 (a1 = 0x9bf80, the 40-byte table codes[5]);
     0x841dc xori a3,a1,-1 (`not`); 0x841e0 bltu a3,a2,0x84218 (the trap branch: 0x9bf80 + 8 r would wrap);
     0x841e4 auipc a2,0x18; 0x841e8 ld a2,-0x74(a2) (the 8 bytes at the .got slot 0x9c170: 0xa4f38);
     0x841ec ld a2,0(a2) (the 8 bytes at 0xa4f38, the runtime's shadow offset cell: 0x7fff8000);
     0x841f0 slli a0,a0,3; 0x841f4 add a0,a1,a0; 0x841f8 srli a1,a0,3; 0x841fc add a1,a1,a2 (the shadow byte's address
     ((0x9bf80 + 8 r) >> 3) + 0x7fff8000); 0x84200 lbu a1,0(a1) and 0x84204 bnez a1,0x8421c (the instrumented check);
     0x84208 ld a0,0(a0) (codes[r]); 0x8420c ld ra,8(sp); 0x84210 addi sp,sp,0x10; 0x84214 ret;
     0x84218 unimp (the trap); 0x8421c jal (the error path of an 8-byte load).
   The table reac_rate_refuse_code.codes is 0x9bf80 in .data.rel.ro (A 0x9bc80); its five words are A's: 0x21600,
   0x21620, 0x21640, 0x21660, 0x21680 (the texts "none" .. "malformed"). r is the 64-bit word in a0 at entry. The only
   store is `sd ra,8(sp)` into the 16-byte save slot [sp - 16, sp) (awr_stk: inside the caller's stack window by the
   contract's window premises); every other byte is only read.
   r >= 5: the entry state holds a0 as its atom; the engine stops at the bgeu 0x841c0, which is split (branch_geu_U):
   the taken side needs r <= 4 and is refuted, the other side forms 0x21600 and runs to the `ret`.
   r = 0 .. 4: the entry state holds a0 as the literal r, so the engine takes the bgeu and forms every value as a
   literal: a2 = 8 r, a1 = 0x9bf80, a3 = 2^64 - 1 - 0x9bf80. THE TRAP BRANCH IS NOT TAKEN: `bltu a3,a2` compares two
   literals, and 8 r <= 32 < 2^64 - 1 - 0x9bf80, so the engine decides it not taken (the U walk's step) and the
   `unimp` at 0x84218 is never stepped. It then reads lib/AU/RtPgRefuse.v's four read-only extents beside the save
   slot: the .got slot [0x9c170, 0x9c178) (0xa4f38, by AR's constant law and the record's as_got_shadow), the shadow
   offset cell [0xa4f38, 0xa4f40) (env slot 32 = 0x7fff8000, by the same law and as_shadow_cell), the five shadow bytes
   of the table at offsets 0x137f0 .. 0x137f4 from slot 32 (each 0: rt_u64tab's 40 addressable bytes) and the table
   [0x9bf80, 0x9bfa8) (rt_u64tab's values).
   WHY THE ERROR PATH IS UNREACHABLE: the shadow byte the `lbu` reads is the literal 0, so the engine decides the
   `bnez` at 0x84204 as not taken; one run reaches the `ret` and the jal at 0x8421c is never stepped. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgRefuse.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the image record's .got slot of the shadow offset cell and that cell (image B: 0x9c170 holds 0xa4f38, the
   runtime's shadow offset cell); the image's symbol record gives both *)
Hypothesis HBgot : as_got_shadow B = 0x9c170.
Hypothesis HBcell : as_shadow_cell B = 0xa4f38.

Theorem rt_refuse_code_B : rt_refuse_code_specX rsegs B MT 0x841b4 RF_TBL RF_COV RF_CS.
Proof using MTL LAWS HBgot HBcell.
change (rt_refuse_code_specX rsegs B MT A_REFUSE RF_TBL RF_COV RF_CS).
unfold rt_refuse_code_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) Hlen Hcov Htab.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_check_STK in Hwlo.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpr : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia).
remember (bv_unsigned (getr regs 10)) as r eqn:Hr.
assert (H10 : getr regs 10 = w64 r) by (subst r; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hr64 : 0 <= r < 2 ^ 64)
by (subst r; pose proof (bv_unsigned_in_range _ (getr regs 10)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; exact Hb).
clear Hr.
unfold cfg_at. change (w64 A_REFUSE) with (Z_to_bv 64 A_REFUSE).
destruct (Z.le_gt_cases 5 r) as [Hge | Hlt].
- (* r >= 5: a0 is its atom; the engine stops at 0x841c0 bgeu a1,a0 (a1 = 4) *)
pose proof (ck_entry A_REFUSE [] W regs memc ltac:(unfold A_REFUSE; lia) (Forall_nil _) Hpr Hsp Hal16) as HS.
rf_env.
rewrite H10 in E10.
rf_run awr_stk. ck_keep kwr_stk.
rf_branch Hb.
+ (* taken: 4 >= r (unsigned), against r >= 5 *)
exfalso. rewrite branch_geu_U in Hb. rewrite (U_lit E 4) in Hb by lia. rewrite (U_atom E 10 r E10 Hr64) in Hb.
destruct (Z.ltb_spec 4 r); cbn in Hb; [discriminate Hb | lia].
+ (* not taken: 0x841c4 auipc / 0x841c8 addi form 0x21600, 0x841cc j 0x8420c; stop at 0x84214 ret *)
rf_run awr_stk. ck_keep kwr_stk.
rf_leaf ltac:(unfold rt_refuse, RF_COV; destruct (Z.leb_spec r 4); [lia | reflexivity]).
- (* r = 0 .. 4: a0 is the literal r; the .got slot and the shadow offset cell by AR's constant law *)
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (rf_entry A_REFUSE [((10%bv : bv 5), SLit r)] W regs memc ltac:(unfold A_REFUSE; lia)) as HS.
lazymatch type of HS with ?P -> _ => assert (HO : P); [|specialize (HS HO); clear HO] end.
{ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite ck_lit. symmetry. exact H10. }
specialize (HS Hpr Hsp Hal16 Kgot Kcell Htab).
rf_env.
assert (Hr04 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) by lia.
(* 0x841b4 .. 0x84210: the bgeu taken (4 >= r); 0x841d0 slli a2 / 0x841d4 auipc / 0x841d8 addi / 0x841dc not and the
   trap branch 0x841e0 bltu a3,a2 on the literals 2^64 - 1 - 0x9bf80 and 8 r, not taken (the unimp at 0x84218 is never
   stepped); every address a literal, the shadow byte the literal 0 so the bnez 0x84204 not taken (the error path at
   0x8421c is never stepped), a0 = codes[r]; stop at 0x84214 ret *)
destruct Hr04 as [-> | [-> | [-> | [-> | ->]]]].
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
Qed.
End c.

Print Assumptions rt_refuse_code_B.
About rt_refuse_code_B.

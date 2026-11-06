(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/RPgCheck.v at fb6520a9cda (its entry state ss_ck, regs_ok_override, the save-slot region and awr_stk / kwr_stk, ck_kept_run, the ret leaf) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_answer 0x82c30 and check_code 0x82c80 against lib/A/RPgCSpec.v's rl_check_answer_specX / rl_check_code_specX on lib/A/Img0.v rsegs. Each function is cut at its calls of the strcmp wrapper (0x41ad0): the run to the call, the call through lib/A/RPgStrcmp.v's aj_strcmp_at (the wrapper's contract astrcmp_realizes is the Section hypothesis ASTRCMP), and a fresh entry state after the call whose save slot holds the caller's ra (and s0) from the extra env slots 33 / 34; the callee-saved registers are threaded across the cuts with cs_eq. The snez-of-xor value lemma is lib/A/RPgCfgChanges.v's snez_xor_Z, restated. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments; RPgStrcmp / rl_cstr /
   rl_cstr_kept / rl_cstr_low become RtPgStrcmp / rt_cstr / rt_cstr_kept / rt_cstr_low; its call-cut plumbing
   (cs_eq .. sp_of_st_ok, pres_of_cs) moved to lib/A/RtPgCheck.v; the walk of role's check_answer (one wrapper call, a
   save slot holding ra only: sc_call, ans_tail) becomes the walk of rate's check_code against lib/A/RtPgCSpec.v's
   rt_check_code_specX, whose call takes a literal chosen by a1 (r = 0: the literal "none"; r = 1 .. 4: an
   instrumented 8-byte load from switch.table.check_code, read through the .got slot / shadow offset cell / shadow
   byte / table regions of lib/A/RtPgRefuse.v's form); role's check_code walk (two calls, s0 saved: L_CODE,
   code_slot, code_mid, code_tail) and its snez-of-xor lemma are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgCheckCode.v at b908b1be5a37, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the theorem names rt_check_*_A -> rt_check_*_B; the Modified-by lines above describe how lib/A/RtPgCheckCode.v was made and quote that file's image-A values; the code below carries image B's values. *)
(* check_code 0x8360c (30 words) of fuzz_rate.asan-ubsan (unstripped sha256
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1; the pinned
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14 has the same loaded bytes), capstone:
     0x8360c addi sp,sp,-0x10; 0x83610 sd ra,8(sp); 0x83614 addiw a1,a1,-1; 0x83618 addi a2,zero,3;
     0x8361c bltu a2,a1,0x83654; 0x83620 auipc a2,0x19; 0x83624 ld a2,-0x4b0(a2) (the .got slot 0x9c170: 0xa4f38);
     0x83628 slli a1,a1,3; 0x8362c ld a2,0(a2) (the shadow offset cell 0xa4f38: 0x7fff8000); 0x83630 auipc a3,0x19;
     0x83634 addi a3,a3,-0x6f0 (a3 = 0x9bf40, switch.table.check_code, 4 entries); 0x83638 add a1,a3,a1;
     0x8363c srli a3,a1,3; 0x83640 add a2,a3,a2; 0x83644 lbu a2,0(a2) and 0x83648 bnez a2,0x8367c (the instrumented
     check); 0x8364c ld a1,0(a1); 0x83650 j 0x8365c; 0x83654 auipc a1,0xfff9e; 0x83658 addi a1,a1,-0x94
     (a1 = 0x215c0, "none"); 0x8365c jal wrapper_strcmp 0x421f4; 0x83660 bnez a0,0x83670; ld ra,8(sp);
     addi sp,sp,0x10; 0x8366c ret; 0x83670 jal __asan_handle_no_return; jal abort; 0x83678 unimp; 0x8367c mv a0,a1;
     jal (the error path of an 8-byte load). Image A's function with one more word, the `unimp` after `jal abort`,
     which no path reaches; the error path after it moves by 4 bytes.
   r is the 64-bit word in a1 at entry, r <= 4 (the contract's premise). Each value of r is its own run: the entry
   state holds a1 as the literal r, so the engine decides the `bltu` (taken for r = 0, where the 32-bit `addiw`
   gives -1, not taken for r = 1 .. 4), and for r = 1 .. 4 forms every address of the table path as a literal and
   reads the four read-only extents beside the save slot (lib/AU/RtPgRefuse.v's .got slot and shadow offset cell, by
   AR's constant law and the record's as_got_shadow / as_shadow_cell; the four shadow bytes of the table at offsets
   0x137e8 .. 0x137eb from env slot 32, each 0 because the table's 32 bytes are addressable, rt_u64tab; the table
   [0x9bf40, 0x9bf60) with its four values, rt_u64tab's).
   WHY THE ABORT AND ERROR PATHS ARE UNREACHABLE. The shadow byte the `lbu` reads is the literal 0, so the `bnez` at
   0x83648 is not taken. The string at a0 has the text of refuse_code(r) (the premise) and the literal a1 holds at
   the call has the text of code_of(r) (the contract's premises on the table entries and on "none"); the two texts
   are equal (RateCfg.code_of_refuse), so the strings meet at the NUL with c1 = c2 = 0 (RtPgStrcmp.v
   str_meet_of_cstr) and the wrapper returns strcmp_res 0 0 = 0; the entry state after the call holds a0 as the
   literal 0, so the engine decides the `bnez` at 0x83660 not taken. The only store is the save of ra into the
   16-byte slot [sp - 16, sp); the wrapper writes only below the callee's sp - 16 (2 ESTACK); so every byte outside
   [sp - T_cmp_STK, sp) is kept. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgStrcmp.
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

(* ---- the image: the function, its code table, its table and literals, the wrapper's entry ---- *)
Definition A_CHECK_CODE : Z := 0x8360c.
Definition A_STRCMP : Z := 0x421f4.
Definition A_CC_RET : Z := 0x83660.
(* switch.table.check_code (0x9bf40, .data.rel.ro): code_of(1 .. 4)'s literals; the literal "none" (0x215c0) *)
Definition CC_TBL : Z := 0x9bf40.
Definition CC_CS : list Z := [0x21540; 0x21560; 0x21580; 0x215a0].
Definition CC_LNONE : Z := 0x215c0.
(* the 30 4-byte words 0x8360c .. 0x83680 *)
Definition sc_tbl : ctable := build_table rsegs A_CHECK_CODE 30 TEmpty.
Lemma sc_tbl_ok : table_ok rsegs sc_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_CODE. lia. Qed.

(* ---- the read-only extents of the table path [lib/AU/RtPgRefuse.v rf_*_region] ---- *)
(* the four shadow bytes of the table, (0x9bf40 >> 3) + 0x7fff8000 = 0x137e8 + 0x7fff8000 and the next three: all 0 *)
Definition cc_sh_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0x137e8 0x137ec 0 0
[YP09.mkChunk 0x137e8 (CVal 1 (SLit 0)); YP09.mkChunk 0x137e9 (CVal 1 (SLit 0));
 YP09.mkChunk 0x137ea (CVal 1 (SLit 0)); YP09.mkChunk 0x137eb (CVal 1 (SLit 0))].
(* the table [0x9bf40, 0x9bf60) *)
Definition cc_tbl_region : YP09.region :=
YP09.mkRegion None 0x9bf40 0x9bf60 0 0
[YP09.mkChunk 0x9bf40 (CVal 8 (SLit 0x21540)); YP09.mkChunk 0x9bf48 (CVal 8 (SLit 0x21560));
 YP09.mkChunk 0x9bf50 (CVal 8 (SLit 0x21580)); YP09.mkChunk 0x9bf58 (CVal 8 (SLit 0x215a0))].
Definition cc_regions : smem := [ ck_stack_region 16; rf_got_region; rf_cell_region; cc_sh_region; cc_tbl_region ].
Definition ss_cc (pc : Z) (ov : list (bv 5 * sv)) : sstate := mkSS pc (ck_sr ov) cc_regions None ck_facts.

Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state of the table path [lib/AU/RtPgRefuse.v rf_entry] *)
Lemma cc_entry : forall pc ov (W : world rsegs) regs memc, 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs ck_extra) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
rdword (aview rsegs (w_H W) memc) 0x9c170 = Some 0xa4f38 ->
rdword (aview rsegs (w_H W) memc) 0xa4f38 = Some SHADOW_OFF ->
rt_u64tab rsegs (w_H W) memc CC_TBL CC_CS ->
st_ok rsegs (Ereg regs ck_extra) (ss_cc pc ov) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov W regs memc Hpc Hov Hpres Hhi Hal Kgot Kcell (_ & _ & _ & Hv & Hsh).
assert (V0 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf40 8 0x21540)
by exact (Hv 0 ltac:(unfold CC_CS; simpl; lia)).
assert (V1 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf48 8 0x21560)
by exact (Hv 1 ltac:(unfold CC_CS; simpl; lia)).
assert (V2 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf50 8 0x21580)
by exact (Hv 2 ltac:(unfold CC_CS; simpl; lia)).
assert (V3 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf58 8 0x215a0)
by exact (Hv 3 ltac:(unfold CC_CS; simpl; lia)).
clear Hv.
assert (Hsh' : forall x, 0x9bf40 <= x < 0x9bf40 + 32 ->
exists s, aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x) = Some s /\ saddr_ok x s)
by (intros x Hx; exact (Hsh x ltac:(unfold CC_TBL, CC_CS; simpl; lia))).
clear Hsh.
rewrite restrict_mkst_fx.
set (E := Ereg regs ck_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 0x7fff8000) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = 0x7fff8000) by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_cc. apply (entry_st_ok_full rsegs); change (Ereg regs ck_extra) with E.
- apply ck_regs_ok. exact Hov.
- vm_compute. reflexivity.
- unfold cc_regions, ck_stack_region, rf_got_region, rf_cell_region, cc_sh_region, cc_tbl_region.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ (* the save slot *)
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
+ (* the .got slot *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 0x9c170 8 (SLit 0xa4f38) 0xa4f38); [reflexivity | zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgot).
+ (* the shadow offset cell *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 0xa4f38 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcell).
+ (* the four shadow bytes of the table: each granule [0x9bf40 + 8 i, 0x9bf40 + 8 i + 8) is fully addressable,
     so each byte is 0 (rf_zero_byte at its last byte) *)
rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137e8 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf40 + 7) _ eq_refl _).
exact (Hsh' (0x9bf40 + 7) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137e9 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf40 + 15) _ eq_refl _).
exact (Hsh' (0x9bf40 + 15) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137ea 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf40 + 23) _ eq_refl _).
exact (Hsh' (0x9bf40 + 23) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137eb 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf40 + 31) _ eq_refl _).
exact (Hsh' (0x9bf40 + 31) ltac:(lia)).
+ (* the table *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
* apply (chunk_ok_val rsegs E _ 0 0x9bf40 8 (SLit 0x21540) 0x21540); [reflexivity | zside | zside | exact V0].
* apply (chunk_ok_val rsegs E _ 0 0x9bf48 8 (SLit 0x21560) 0x21560); [reflexivity | zside | zside | exact V1].
* apply (chunk_ok_val rsegs E _ 0 0x9bf50 8 (SLit 0x21580) 0x21580); [reflexivity | zside | zside | exact V2].
* apply (chunk_ok_val rsegs E _ 0 0x9bf58 8 (SLit 0x215a0) 0x215a0); [reflexivity | zside | zside | exact V3].
- (* the five extents are pairwise disjoint: sp in [2^46, 2^47] lies above all of them *)
apply pairwise_disjoint_of_extents.
unfold cc_regions, ck_stack_region, rf_got_region, rf_cell_region, cc_sh_region, cc_tbl_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [ck_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
End b0.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- the save slot of the run before the call: the value of one of its chunks ---- *)
Lemma st_ok_region_nth : forall H E ss ms i r,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

(* ---- strings kept by a write at or above 2^46 ---- *)
Lemma rt_cstr_kept : forall H (m m' : word -> option byte) a s lo hi,
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview rsegs H m' x = aview rsegs H m x) -> 2 ^ 46 <= lo ->
rt_cstr rsegs H m a s -> rt_cstr rsegs H m' a s.
Proof.
intros H m m' a s lo hi HK Hlo (Hc & Hn & Hf & Ha0 & Hhi & Himg & Ham & Hra & Hhv).
assert (Hlow : forall i, 0 <= i <= Z.of_nat (length s) -> 0 <= a + i < kLowMemEnd)
by (intros i Hi; apply ck_segs_low; apply Himg; exact Hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Kx : forall x, 0 <= x < 2 ^ 46 -> aview rsegs H m' x = aview rsegs H m x) by (intros x Hx; apply HK; lia).
assert (Hsh : forall x, a <= x <= a + Z.of_nat (length s) -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46).
{ intros x Hx. pose proof (Hlow (x - a) ltac:(lia)) as Hl. unfold shadow_of_addr, SHADOW_OFF. rewrite C5 in Hl.
assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
split; [intros i Hi; rewrite Kx by (pose proof (Hlow i ltac:(lia)); rewrite C5 in *; lia); exact (Hc i Hi)|].
split; [rewrite Kx by (pose proof (Hlow (Z.of_nat (length s)) ltac:(lia)); rewrite C5 in *; lia); exact Hn|].
split; [exact Hf|]. split; [exact Ha0|]. split; [exact Hhi|]. split; [exact Himg|]. split; [exact Ham|].
split.
- intros x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite Kx; [exact Hsv | apply Hsh; lia].
- intros t Ht. rewrite Kx; [exact (Hhv t Ht)|].
pose proof (Hlow 0 ltac:(lia)) as L0. pose proof (Hlow (Z.of_nat (length s)) ltac:(lia)) as L1.
unfold shadow_addr, SHADOW_OFF in Ht. rewrite C5 in L0, L1.
replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Ht by lia.
assert (0 <= a / 8) by (apply Z.div_pos; lia).
assert ((a + Z.of_nat (length s)) / 8 <= a + Z.of_nat (length s)) by (apply Z.div_le_upper_bound; lia).
assert (0 <= (0x7fff8000 + a / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
assert ((0x7fff8000 + (a + Z.of_nat (length s)) / 8) / 8 * 8 <= 0x7fff8000 + (a + Z.of_nat (length s)) / 8)
by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
lia.
Qed.
End a.

(* ---- the entry state after the call ---- *)
(* env Ereg regs2 [shadow base; ra0; s00]: slot 33 holds the caller's ra; a0 is the literal 0 (the wrapper's
   answer); the save slot [sp, sp + 16) at the call's sp holds the chunks cs *)
Definition sc_extra (ra0 s00 : word) : list word := [Z_to_bv 64 ck_SB; ra0; s00].
Definition sc_slot (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 cs.
Definition ss_ret (pc : Z) (cs : list YP09.chunk) : sstate :=
mkSS pc (ck_sr [((10%bv : bv 5), SLit 0)]) [sc_slot cs] None ck_facts.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma sc_ret_entry : forall pc cs (W : world rsegs) regs2 ra0 s00 memc, 0 <= pc ->
getr regs2 (10%bv : bv 5) = w64 0 ->
2 ^ 46 <= spZ regs2 <= 2 ^ 47 - 16 -> spZ regs2 mod 16 = 0 ->
Forall (YP09.chunk_ok rsegs (Ereg regs2 (sc_extra ra0 s00)) (mrestrict (w_H W) memc) (spZ regs2)) cs ->
regions_wf [sc_slot cs] = true ->
st_ok rsegs (Ereg regs2 (sc_extra ra0 s00)) (ss_ret pc cs)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc cs W regs2 ra0 s00 memc Hpc H10 Hsp Hal Hcs Hwf.
rewrite restrict_mkst_fx.
set (E := Ereg regs2 (sc_extra ra0 s00)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs2) by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
unfold ss_ret. apply (entry_st_ok_full rsegs); change (Ereg regs2 (sc_extra ra0 s00)) with E.
- apply ck_regs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
+ intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
+ rewrite ck_lit. symmetry. exact H10.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok, sc_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. exact Hcs.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [ck_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
End b.

(* ---- the run and the model chain on this file's table [RtPgCheck.v ck_run] ---- *)
Lemma same_io_wvb_sc : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
Ltac sc_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok sc_tbl_ok HS HJ SHOK ck_Bspan; [awr | ] end.
Ltac kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_sc]; kio].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the image record's .got slot of the shadow offset cell and that cell [lib/AU/RtPgRefuse.v] *)
Hypothesis HBgot : as_got_shadow B = 0x9c170.
Hypothesis HBcell : as_shadow_cell B = 0xa4f38.
(* the strcmp wrapper's contract at its 4-byte jump 0x421f4 (lib/Reusable/AStrcmpDef.v, fuzz_identity's text); the
   wrapper's walk discharges it *)
Hypothesis ASTRCMP : astrcmp_realizes rsegs B A_STRCMP.

(* a string of the image lies below kLowMemEnd, so below every stack address *)
Lemma rt_cstr_low : forall H m a s, rt_cstr rsegs H m a s ->
forall b, a <= b <= a + Z.of_nat (length s) -> 0 <= b < kLowMemEnd.
Proof.
intros H m a s (_ & _ & _ & _ & _ & Himg & _) b Hb. replace b with (a + (b - a)) by lia. apply ck_segs_low. apply Himg. lia.
Qed.
Lemma mod16_off : forall sp sp0 c, sp mod 16 = 0 -> sp0 mod 16 = 0 -> c mod 16 = 0 -> (sp - c - sp0) mod 16 = 0.
Proof.
intros sp sp0 c H1 H2 H3.
pose proof (Z.div_mod sp 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
pose proof (Z.div_mod c 16 ltac:(lia)) as D3.
rewrite H1 in D1. rewrite H2 in D2. rewrite H3 in D3.
replace (sp - c - sp0) with ((sp / 16 - c / 16 - sp0 / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* ---- one call of the wrapper on two strings of the same text, from a caller whose save slot is at sp - 16 ---- *)
(* The call state: a0 = x, a1 = y, ra = raw, sp = the caller's entry sp minus 16; both strings hold the text t
   (at the caller's entry memory memc, and kept since: KT keeps every byte outside [klo, sp)). After the call
   the wrapper's answer is 0, every callee-saved register is as at the call, and only [sp - 16 - 2 ESTACK, sp - 16)
   changed. *)
Lemma sc_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) regsT memT mdT
x y (t : list Z) raw klo (Q : world rsegs -> config -> Prop),
rt_cpre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
getr regsT (10%bv : bv 5) = w64 x -> getr regsT (11%bv : bv 5) = w64 y -> getr regsT (1%bv : bv 5) = raw ->
YK0s.ret_ok raw -> spZ regsT = spZ regs - 16 -> cs_eq L_ANS regs regsT ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (klo <= a < spZ regs) -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a) ->
2 ^ 46 <= klo ->
rt_cstr rsegs (w_H W) memc x t -> rt_cstr rsegs (w_H W) memc y t -> Z.of_nat (length t) < 2 ^ 31 ->
(forall regs2 mem2 md2,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
aregs_preserved regsT regs2 -> same_io mdT md2 -> getr regs2 (10%bv : bv 5) = w64 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 - 2 * ESTACK <= a < spZ regs - 16) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) ->
SRr rsegs W (mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_STRCMP) memT (seg_rom rsegs)) mdT) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsT memT mdT x y t raw klo Q
HP HJT R10 R11 R1 Hraw RSP HCS KT Hklo Hx Hy Hlen K.
destruct HP as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_cmp_STK in Hwlo.
assert (HxT : rt_cstr rsegs (w_H W) memT x t) by (eapply rt_cstr_kept; [exact KT | exact Hklo | exact Hx]).
assert (HyT : rt_cstr rsegs (w_H W) memT y t) by (eapply rt_cstr_kept; [exact KT | exact Hklo | exact Hy]).
pose proof (rt_cstr_low _ _ _ _ HxT) as Lx. pose proof (rt_cstr_low _ _ _ _ HyT) as Ly.
destruct (str_meet_of_cstr rsegs t W memT x t y (cstr_at_of_rt_cstr rsegs W memT x t HxT)
(cstr_at_of_rt_cstr rsegs W memT y t HyT)) as (kk & c1 & c2 & Hmeet & Hk1 & Hk2 & Hres).
assert (H0 : strcmp_res c1 c2 = 0) by (apply Hres; reflexivity).
assert (Hwin : forall b, (x <= b <= x + Z.of_nat (length t) \/ y <= b <= y + Z.of_nat (length t)) ->
~ (spZ regsT - ESTACK <= b < spZ regsT)).
{ intros b [Hb|Hb]; [pose proof (Lx b Hb) | pose proof (Ly b Hb)]; rewrite C5 in *; lia. }
destruct (rt_cstr_args rsegs W regsT memT x t kk HxT ltac:(lia) ltac:(intros b Hb; apply Hwin; left; exact Hb))
as (Hx0 & Hxk & Hsx & Hmx & Hrx & Hhx).
destruct (rt_cstr_args rsegs W regsT memT y t kk HyT ltac:(lia) ltac:(intros b Hb; apply Hwin; right; exact Hb))
as (Hy0 & Hyk & Hsy & Hmy & Hry & Hhy).
assert (G3 : getr regsT 3 = w64 (as_gp B)) by (rewrite (HCS (3%bv : bv 5) ltac:(cbv [L_ANS In]; left; reflexivity)); exact Hgp).
assert (G4 : getr regsT 4 = w64 (as_tp B)) by (rewrite (HCS (4%bv : bv 5) ltac:(cbv [L_ANS In]; right; left; reflexivity)); exact Htp).
eapply SRr_bind.
{ eapply (aj_strcmp_at rsegs B LAWS ck_segs_low A_STRCMP ASTRCMP W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k x y kk c1 c2 (spZ regs - 16 - sp0) raw HJT
R10 R11 Hx0 Hy0 ltac:(lia) Hxk Hyk Hmeet ltac:(lia) (mod16_off _ _ 16 Hal16 Hsp0al eq_refl) ltac:(lia) ltac:(lia)
G3 G4 R1 Hraw Hsx Hsy); try (intros a Ha; pose proof (Lx a ltac:(lia)); rewrite C5 in *; lia);
try (intros a Ha; pose proof (Ly a ltac:(lia)); rewrite C5 in *; lia); assumption. }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & H10 & HK2 & _).
apply K; [exact HJ2 | exact HP2 | exact Hsame | rewrite H10, H0; reflexivity |].
intros a Ha Hn. apply HK2; [exact Ha|]. intros Hw. apply Hn. lia.
Qed.

(* the value of the save slot's chunk at sp - 8 after the run to the call: the caller's ra *)
Ltac slot_val HS B2 E1 Hv rgs :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
lazymatch r with Some ?rg =>
let Hr := fresh "Hr" in assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
let Hreg := fresh "Hreg" in pose proof (st_ok_region_nth _ _ _ _ 0 _ HS Hr) as Hreg; clear Hr;
pose proof (field_of_region _ _ _ _ _ _ _ _ _ (-8) 8 (SOff 1 0) (raZ rgs) Hreg B2) as Hv;
clear Hreg;
specialize (Hv ltac:(cbn; tauto));
specialize (Hv ltac:(apply bv_eq; rewrite denot_SOff, Z.add_0_r, E1; unfold raZ; rewrite Z_to_bv_bv_unsigned;
  apply zcanon_id; pose proof (bv_unsigned_in_range _ (getr rgs 1)) as Hbnd; change (bv_modulus 64) with (2 ^ 64) in Hbnd;
  unfold M64; lia));
specialize (Hv ltac:(unfold raZ; pose proof (bv_unsigned_in_range _ (getr rgs 1)) as Hbnd;
  change (bv_modulus 64) with (2 ^ 64) in Hbnd; cbn; lia) ltac:(cbn; lia));
change (N.to_nat 8) with 8%nat in Hv
end end.

(* check_code after its call: the entry state at 0x83660 (a0 = 0, the slot [sp - 16, sp) holding ra at sp - 8),
   one run through `bnez a0` (not taken), `ld ra,8(sp)`, `addi sp,sp,0x10` to the ret, and the leaf. *)
Lemma cc_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) regsT memT mdT
x y (t : list Z),
rt_cpre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
same_io mdc mdT ->
getr regsT (10%bv : bv 5) = w64 x -> getr regsT (11%bv : bv 5) = w64 y ->
getr regsT (1%bv : bv 5) = w64 A_CC_RET -> spZ regsT = spZ regs - 16 -> cs_eq L_ANS regs regsT ->
val_mem rsegs (mrestrict (w_H W) memT) (spZ regs - 8) 8 (raZ regs) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a) ->
rt_cstr rsegs (w_H W) memc x t -> rt_cstr rsegs (w_H W) memc y t -> Z.of_nat (length t) < 2 ^ 31 ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_STRCMP) memT (seg_rom rsegs)) mdT)
(rt_cpost rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).
Proof using MTL LAWS ASTRCMP.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsT memT mdT x y t
HP HJT HioT R10 R11 R1 RSP HCS HSLOT KT Hx Hy Hlen.
pose proof HP as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_cmp_STK in Hwlo.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
apply (sc_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsT memT mdT x y t (w64 A_CC_RET) (spZ regs - 16) _
HP HJT R10 R11 R1 ltac:(vm_compute; reflexivity) RSP HCS KT ltac:(lia) Hx Hy Hlen).
intros regs2 mem2 md2 HJ HP2 Hsame H10 HK2.
assert (SP2 : spZ regs2 = spZ regs - 16).
{ rewrite <- RSP. unfold spZ. f_equal. exact (HP2 2 ltac:(unfold acallee_saved; lia)). }
assert (HV2 : val_mem rsegs (mrestrict (w_H W) mem2) (spZ regs2 + 8) 8 (raZ regs)).
{ rewrite SP2. replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia.
eapply (val_mem_kept rsegs); [|exact HSLOT]. intros kk Hkk. apply HK2; [lia | change (Z.of_nat 8) with 8 in Hkk; lia]. }
pose proof (sc_ret_entry A_CC_RET [YP09.mkChunk 8 (CVal 8 (SOff 33 0))] W regs2 (getr regs 1) (Z_to_bv 64 0) mem2
ltac:(unfold A_CC_RET; lia) H10 ltac:(rewrite SP2; lia) ltac:(rewrite SP2; pose proof (mod16_off _ 0 16 Hal16 eq_refl eq_refl) as M16; rewrite Z.sub_0_r in M16; exact M16))
as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val rsegs _ _ _ 8 8 (SOff 33 0) (raZ regs)); [
apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [sc_extra nth];
unfold raZ; rewrite Z_to_bv_bv_unsigned; apply zcanon_id; pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb;
change (bv_modulus 64) with (2 ^ 64) in Hb; unfold M64; lia
| unfold raZ; pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; cbn; lia
| cbn; lia
| exact HV2 ])
ltac:(vm_compute; reflexivity)).
remember (Ereg regs2 (sc_extra (getr regs 1) (Z_to_bv 64 0))) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 (sc_extra (getr regs 1) (Z_to_bv 64 0))) E) by (subst E; apply env_agree_refl).
assert (E33 : ew E 33 = getr regs 1) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B2 : bv_unsigned (ew E 2) = spZ regs2) by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
clear HE.
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem2 a)
by (intros; reflexivity).
change (w64 A_CC_RET) with (Z_to_bv 64 A_CC_RET).
(* 0x83660 bnez a0 (a0 = 0: not taken), ld ra,8(sp), addi sp,sp,0x10; stop at 0x8366c ret *)
sc_run awr_stk. ck_keep kwr_stk.
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (sp_of_st_ok _ _ ss ms regs2 _ 16 HS HAE ltac:(vm_compute; reflexivity)) as SPF;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ L_ANS HS HAE ltac:(vm_compute; reflexivity)) as CSF
end;
eapply (SRr_ret_at rsegs sc_tbl sc_tbl_ok ck_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
cbv beta delta [rt_cpost rt_cpost_g]; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists.
split; [rewrite R1', E33, Hra; reflexivity|].
split; [reflexivity|].
split; [eapply ajournal_materialize; eassumption|].
split.
{ apply pres_of_cs.
- eapply cs_eq_trans; [exact HCS|]. eapply cs_eq_trans; [exact (cs_eq_of_pres L_ANS _ _ L_ANS_cs HP2)|]. exact CSF.
- rewrite SPF, SP2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. apply zcanon_id. unfold M64. lia. }
split; [reflexivity|].
split; [exact I|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [exact HioT|]; eapply same_io_trans; [exact Hsame|]; kio|].
split; [apply mo_le_refl; assumption|].
split; [|exact I].
intros a Ha Hz _. rewrite (KE a Ha (fun z => z)).
rewrite (HK2 a Ha ltac:(intros Hw; apply Hz; unfold T_cmp_STK; lia)).
apply KT; [exact Ha|]. intros Hw; apply Hz; unfold T_cmp_STK; lia.
Qed.

(* the env facts after the entry state is posed as HS, for the argument s in a0 (H10) [RtPgRefuse.v rf_env] *)
Ltac cc_env H10 :=
lazymatch type of H10 with getr ?regs _ = w64 ?s =>
lazymatch goal with HS : st_ok _ (Ereg regs ck_extra) _ (restrict (w_H ?W) (mkst _ _ ?memc _)) |- _ =>
remember (Ereg regs ck_extra) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs ck_extra) E) by (subst E; apply env_agree_refl);
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
assert (E10 : ew E 10 = Z_to_bv 64 s) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10);
clear HE;
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) memc)) by constructor;
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity)
end end.
(* the run from the entry to the wrapper's entry, and the tail: x = s in a0 (untouched), y the literal in a1, both
   with the text t *)
Ltac cc_to_call x y t Hx Hy :=
sc_run awr_stk; ck_keep kwr_stk;
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 (Ereg ?rg _) ?E,
  B2 : bv_unsigned (ew ?E 2) = spZ ?rg, E1 : ew ?E 1 = getr ?rg 1 |- _ =>
let R10' := fresh "R10'" in rreg HS (10%bv : bv 5) R10';
let R11' := fresh "R11'" in rreg HS (11%bv : bv 5) R11';
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
let Hv := fresh "Hv" in slot_val HS B2 E1 Hv rg;
let SPT := fresh "SPT" in let CST := fresh "CST" in
pose proof (sp_of_st_ok _ _ ss ms rg _ (-16) HS HAE ltac:(vm_compute; reflexivity)) as SPT;
pose proof (cs_eq_of_st_ok _ _ ss ms rg _ L_ANS HS HAE ltac:(vm_compute; reflexivity)) as CST;
rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
replace (ss_pc ss) with A_STRCMP by (vm_compute; reflexivity);
lazymatch goal with HP : rt_cpre _ _ _ _ _ _ _ _ _ _ _ _ _ rg _ _ _ _ _, E10 : ew E 10 = _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
eapply (cc_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rg _ _ _ x y t HP);
[ eassumption | kio | rewrite R10', E10; reflexivity | rewrite R11'; reflexivity | rewrite R1'; reflexivity
| rewrite SPT; apply zcanon_id; unfold M64; lia | exact CST | replace (spZ rg - 8) with (spZ rg + -8) by lia; exact Hv
| exact KE | exact Hx | exact Hy | vm_compute; reflexivity ]
end end.
(* one value i = 1 .. 4 of r: the table path's entry state, then the run to the call and the tail *)
Ltac cc_tbl_case i y W regs memc H10 H11 Hpr Hsp Hal16 Kgot Kcell Htab Hs Hlit :=
let HS := fresh "HS" in
pose proof (cc_entry A_CHECK_CODE [((11%bv : bv 5), SLit i)] W regs memc ltac:(unfold A_CHECK_CODE; lia)) as HS;
lazymatch type of HS with ?P -> _ => let HO := fresh "HO" in assert (HO : P); [|specialize (HS HO); clear HO] end;
[ apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
  [ let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
  | rewrite ck_lit; symmetry; exact H11 ]
| ];
specialize (HS Hpr Hsp Hal16 Kgot Kcell Htab);
cc_env H10;
let Hy := fresh "Hy" in
lazymatch type of Hs with rt_cstr _ ?Hh ?mm ?s ?t =>
assert (Hy : rt_cstr rsegs Hh mm y t) by exact (Hlit (i - 1) ltac:(lia));
cc_to_call s y t Hs Hy
end.

(* check_code(got, r) *)
Theorem rt_check_code_B : rt_check_code_specX rsegs B MT A_CHECK_CODE CC_TBL CC_LNONE CC_CS.
Proof using MTL LAWS HBgot HBcell ASTRCMP.
unfold rt_check_code_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s HP H10 Hr4 Hs Hlen Htab Hlit Hln.
pose proof HP as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hwlo' : sp0 - STK <= spZ regs - 16) by (unfold T_cmp_STK in Hwlo; lia).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpr : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia).
remember (bv_unsigned (getr regs 11)) as r eqn:Hr.
assert (H11 : getr regs 11 = w64 r) by (subst r; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hr0 : 0 <= r)
by (subst r; pose proof (bv_unsigned_in_range _ (getr regs 11)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; lia).
clear Hr.
(* the argument's text is code_of(r)'s (RateCfg.code_of_refuse) *)
assert (Htxt : rt_refuse_txt r = rt_code_of_txt r)
by (unfold rt_refuse_txt, rt_code_of_txt; rewrite RateCfg.code_of_refuse by lia; reflexivity).
rewrite Htxt in Hs. clear Htxt.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
assert (Hr04 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) by lia.
unfold cfg_at. change (w64 A_CHECK_CODE) with (Z_to_bv 64 A_CHECK_CODE).
destruct Hr04 as [-> | [-> | [-> | [-> | ->]]]].
- (* r = 0: 0x8361c bltu taken (a1 = -1 after the 32-bit addiw), a1 := "none" 0x215c0, 0x8365c jal: stop at 0x421f4 *)
pose proof (ck_entry A_CHECK_CODE [((11%bv : bv 5), SLit 0)] W regs memc ltac:(unfold A_CHECK_CODE; lia)) as HS.
lazymatch type of HS with ?P -> _ => assert (HO : P); [|specialize (HS HO); clear HO] end.
{ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite ck_lit. symmetry. exact H11. }
specialize (HS Hpr Hsp Hal16).
cc_env H10.
cc_to_call s CC_LNONE (rt_code_of_txt 0) Hs Hln.
- (* r = 1: 0x8361c bltu not taken, the table path (the shadow byte 0, the bnez at 0x83648 not taken),
     a1 := code_of(1)'s literal 0x21540, 0x8365c jal: stop at 0x421f4 *)
cc_tbl_case 1 0x21540 W regs memc H10 H11 Hpr Hsp Hal16 Kgot Kcell Htab Hs Hlit.
- (* r = 2: a1 := 0x21560 *)
cc_tbl_case 2 0x21560 W regs memc H10 H11 Hpr Hsp Hal16 Kgot Kcell Htab Hs Hlit.
- (* r = 3: a1 := 0x21580 *)
cc_tbl_case 3 0x21580 W regs memc H10 H11 Hpr Hsp Hal16 Kgot Kcell Htab Hs Hlit.
- (* r = 4: a1 := 0x215a0 *)
cc_tbl_case 4 0x215a0 W regs memc H10 H11 Hpr Hsp Hal16 Kgot Kcell Htab Hs Hlit.
Qed.
End c.

Print Assumptions rt_check_code_B.

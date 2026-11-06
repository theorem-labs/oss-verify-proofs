(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/RPgCheck.v at fb6520a9cda (its entry state, save-slot region, run / keep / leaf chain and write obligations, reused by Require) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_refuse_code 0x82e6c against lib/A/RPgCSpec.v's rl_refuse_code_specX on the concrete image lib/A/Img0.v rsegs, with its own code table (23 words from 0x82e6c), the a0 clause of lib/A/RPgCfgChanges.v's cfg_leaf and its cfg_branch split, and the .got-slot / shadow-offset-cell regions of proofs/libreac/fuzz_knock/lib/A/ACeh.v got_region / bcell_region at origin/ossv/recipes 6ebe35ba632 (with lib/A/APgRt.v's al_const / chunk_ok_val / val_mem_of_rdword proofs of them); new: the regions of the two shadow bytes of the table and of the table itself, and the split on a0 (r >= 2: one branch; r = 0, r = 1: a0 a literal). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgRefuse.v and lib/A/RPgCheck.v at 77f59d02b01
   (the save-slot region, its write obligation awr_stk / kwr_stk, the .got-slot and shadow-offset-cell regions with
   their proofs from AR's constant law, the zero-shadow-byte lemma, the overrides of the entry registers, the run /
   keep / branch chain and the `ret` leaf) for reac-pw/fuzz_rate's image A (fuzz_rate.asan): it walks check_list
   0x837a8 against lib/A/RtPgCSpec.v's rt_check_list_specX on the image module's loaded segments, with the plumbing
   lemmas of lib/A/RtPgLeaf.v; new: the regions of closed_list's 12 bytes and of its two shadow bytes (the second
   one any value range_addressable allows at offset 11), the four cases on hz and the five on that shadow byte, the
   two loops run with every iteration's compare decided or split, and the mask tail split on the three bit tests. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgCheckList.v at a2647881ba31, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the theorem names rt_*_A -> rt_*_B; the Modified-by lines above describe how lib/A/RtPgCheckList.v was made and quote that file's image-A values; the code below carries image B's values. *)
(* check_list(hz, bit, closed, mask, best), 0x83684, 316 bytes, 79 words (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; symbols from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, the same loaded bytes):
     0x83684 addi sp,sp,-16; sd ra,8(sp); li a7,0; auipc a5,0x19; ld a5,-1312(a5) (the 8 bytes at the .got slot 0x9c170:
       0xa4f38); 0x83698 ld a6,0(a5) (the 8 bytes at 0xa4f38, the runtime's shadow offset cell: 0x7fff8000);
       auipc a5,0xfff9e; addi t0,a5,-380 (t0 = closed_list 0x21520); li t1,3; mv a5,t0;
     first loop 0x836ac: srli t2,a5,3; add t2,t2,a6; lb t2,0(t2) (the shadow byte of a5); bnez t2,0x836dc;
       0x836bc lw t2,0(t0); beq a0,t2,0x836f0; addi a7,a7,1; addi t1,t1,-1; addi a5,a5,4; addi t0,t0,4;
       bnez t1,0x836ac; j 0x836fc;
       0x836dc andi t3,a5,7; addi t3,t3,3; blt t3,t2,0x836bc; mv a0,a5; jal (the error path of a 4-byte load);
       0x836f0 li a5,1; sllw a5,a5,a7; j 0x83700; 0x836fc li a5,0; 0x83700 bne a1,a5,0x837b4;
     second loop: auipc a1,0xfff9e; addi a5,a1,-484 (a5 = 0x21520); li a7,2; mv a1,a5;
       0x83714 srli t0,a1,3; add t0,t0,a6; lb t1,0(t0); mv t0,a7; bnez t1,0x83744; 0x83728 lw t1,0(a5);
       beq a0,t1,0x83758; addi a7,t0,-1; addi a1,a1,4; addi a5,a5,4; bnez t0,0x83714; j 0x83758;
       0x83744 andi a7,a1,7; addi a7,a7,3; blt a7,t1,0x83728; mv a0,a1; jal (the error path of a 4-byte load);
       0x83758 xor a0,a0,t1; seqz a0,a0; bne a2,a0,0x837b4;
     mask tail: andi a0,a3,4; bnez a0,0x83790; andi a0,a3,2; bnez a0,0x837a8; slli a3,a3,0x3f; lui a0,0xb;
       srai a3,a3,0x3f; addiw a0,a0,-956; and a0,a3,a0; beq a4,a0,0x8379c; j 0x837b4;
       0x83790 lui; addiw a0 = 96000; bne a4,a0,0x837b4; 0x8379c ld ra,8(sp); addi sp,sp,16; 0x837a4 ret;
       0x837a8 lui; addiw a0 = 48000; beq a4,a0,0x8379c; 0x837b4 jal (the no-return helper); jal abort;
       0x837bc unimp (after the call of abort, which does not return: no path reaches it).
   The only store is `sd ra,8(sp)` into the 16-byte save slot [sp - 16, sp) (awr_stk: inside the caller's stack
   window by the contract's two window premises); every other byte is only read: the .got slot [0x9c170, 0x9c178)
   and the shadow offset cell [0xa4f38, 0xa4f40) (AR's constant law with the record's as_got_shadow = 0x9c170 and
   as_shadow_cell = 0xa4f38, the two Section hypotheses HBgot / HBcell, measured on the pinned file: the word at
   0x9c170 is 0xa4f38), closed_list [0x21520, 0x2152c) (rt_i32tab: 44100, 48000, 96000) and its two shadow bytes at
   offsets 0x42a4 and 0x42a5 from env slot 32 = 0x7fff8000.
   The shadow bytes: the granule [0x21520, 0x21528) is fully addressable (rt_i32tab's range_addressable at its last
   byte), so its shadow byte is 0; the granule from 0x21528 has only [0x21528, 0x2152c) in the table, and
   range_addressable at 0x2152b allows its shadow byte s to be 0 or 4 .. 7. The walk splits on s; each value is a
   literal of the region, so the engine decides `bnez t2` / `blt t3,t2` (3 < s) itself.
   The cases on hz (RateCfg.rate_bit_cases): for 44100, 48000 and 96000, a0, a1 = rate_bit hz and a2 =
   rate_closed hz are literals of the entry state (the contract's premises), so the engine runs both loops with every
   compare decided, through `bne a1,a5` and `bne a2,a0`, to the first mask test (the shadow byte s is read only for
   96000). For any other hz, a0 is its atom: the engine stops at the first loop's three `beq a0,t2` (t2 = 44100,
   48000, 96000), each split, the taken side refuted by hz's case; the second loop's compares it decides from those
   conditions, and it stops at `bne a2,a0` with a0 = seqz (hz xor 96000), whose taken side is refuted (hz <> 96000).
   The mask tail: the engine stops at each bit test on the atom mask (split; the side's bit fact) and at the compare
   of a4 (the atom of a4 = rate_best mask) with the constant of that side; the side that jumps to 0x837b4 is refuted by
   RateCfg.rate_best on the bit facts, the other runs to the `ret` at 0x837a4.
   WHY THE ABORT AND THE ERROR PATHS ARE UNREACHABLE: each jal to 0x837b4 sits on a refuted side; each error path sits
   behind a shadow byte that is a literal the engine decides (0, or 3 < s for s in 4 .. 7). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgLeaf.
From OSSVerify.reac_pw.fuzz_rate.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image: check_list's 79 words (the last the unimp after `jal abort`), the table the engine reads its code
   from ---- *)
Local Notation rsegs := AsanUbsan.M.loaded_segments.
Definition A_CHECK_LIST : Z := 0x83684.
Definition cl_tbl : ctable := build_table rsegs A_CHECK_LIST 79 TEmpty.
Lemma cl_tbl_ok : table_ok rsegs cl_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_LIST. lia. Qed.

(* ---- the entry state's regions (base None: absolute addresses; base Some 32: offsets from env slot 32 =
   0x7fff8000; base Some 2: offsets from sp) ---- *)
(* the save slot [sp - 16, sp) *)
Definition cl_stack_region (frame : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- frame) 0 (- frame) 0 [].
(* the .got slot [0x9c170, 0x9c178): the address of the shadow offset cell *)
Definition cl_got_region : YP09.region :=
YP09.mkRegion None 0x9c170 0x9c178 0 0 [YP09.mkChunk 0x9c170 (CVal 8 (SLit 0xa4f38))].
(* the shadow offset cell [0xa4f38, 0xa4f40): 0x7fff8000, the atom of env slot 32 *)
Definition cl_cell_region : YP09.region :=
YP09.mkRegion None 0xa4f38 0xa4f40 0 0 [YP09.mkChunk 0xa4f38 (CVal 8 (SOff 32 0))].
(* the shadow byte of closed_list's first granule, (0x21520 >> 3) + 0x7fff8000: 0 *)
Definition cl_sh1_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0x42a4 0x42a5 0 0 [YP09.mkChunk 0x42a4 (CVal 1 (SLit 0))].
(* the same and the next one, s *)
Definition cl_sh2_region (s : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) 0x42a4 0x42a6 0 0 [YP09.mkChunk 0x42a4 (CVal 1 (SLit 0)); YP09.mkChunk 0x42a5 (CVal 1 (SLit s))].
(* closed_list [0x21520, 0x2152c) *)
Definition cl_tab_region : YP09.region :=
YP09.mkRegion None 0x21520 0x2152c 0 0
[YP09.mkChunk 0x21520 (CVal 4 (SLit 44100)); YP09.mkChunk 0x21524 (CVal 4 (SLit 48000));
 YP09.mkChunk 0x21528 (CVal 4 (SLit 96000))].
Definition cl_regions (sh : YP09.region) : smem := [ cl_stack_region 16; cl_got_region; cl_cell_region; sh; cl_tab_region ].
(* sp in [2^46, 2^47], 16-aligned: the save slot lies outside the shadow band *)
Definition cl_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] [].
(* the entry registers: sr_atoms with the overrides ov (register, value the contract fixes) *)
Definition cl_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
Definition ss_cl (pc : Z) (ov : list (bv 5 * sv)) (sh : YP09.region) : sstate := mkSS pc (cl_sr ov) (cl_regions sh) None cl_facts.

(* an override of a register by a value it already has keeps regs_ok *)
Lemma cl_regs_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma cl_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (cl_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold cl_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply cl_regs_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.

(* a shadow byte s of an address x with x mod 8 = 7 that range_addressable accepts is 0 *)
Lemma cl_zero_byte : forall H mem x a, x mod 8 = 7 ->
(exists s, aview rsegs H mem a = Some s /\ saddr_ok x s) -> val_mem rsegs (mrestrict H mem) a 1 0.
Proof.
intros H mem x a Hx (s & Hs & Hok).
destruct Hok as [-> | [H1 H2]]; [|lia].
apply aview_byte in Hs as (b & Hb & Hv & _).
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite <- Hv. first [reflexivity | vm_compute; reflexivity].
Qed.
(* a byte the view reads as s holds s *)
Lemma cl_any_byte : forall H mem a s, aview rsegs H mem a = Some s -> val_mem rsegs (mrestrict H mem) a 1 s /\ 0 <= s < 256.
Proof.
intros H mem a s Hs.
apply aview_byte in Hs as (b & Hb & Hv & Hr). split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal.
rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. subst s.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma cl_sh1_ok : forall regs (H : word -> bool) memc,
val_mem rsegs (mrestrict H memc) (0x7fff8000 + 0x42a4) 1 0 ->
region_ok rsegs (Ereg regs lf_extra) (mrestrict H memc) cl_sh1_region.
Proof.
intros regs H memc Z0.
assert (E32 : ew (Ereg regs lf_extra) 32 = Z_to_bv 64 0x7fff8000) by exact (ew_Ereg_extra regs _ 0).
unfold region_ok, cl_sh1_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs _ _ 0x7fff8000 0x42a4 1 (SLit 0) 0); [reflexivity | zside | zside | exact Z0].
Qed.
Lemma cl_sh2_ok : forall regs (H : word -> bool) memc s, 0 <= s < 256 ->
val_mem rsegs (mrestrict H memc) (0x7fff8000 + 0x42a4) 1 0 ->
val_mem rsegs (mrestrict H memc) (0x7fff8000 + 0x42a5) 1 s ->
region_ok rsegs (Ereg regs lf_extra) (mrestrict H memc) (cl_sh2_region s).
Proof.
intros regs H memc s Hs Z0 Z1.
assert (E32 : ew (Ereg regs lf_extra) 32 = Z_to_bv 64 0x7fff8000) by exact (ew_Ereg_extra regs _ 0).
unfold region_ok, cl_sh2_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
- apply (chunk_ok_val rsegs _ _ 0x7fff8000 0x42a4 1 (SLit 0) 0); [reflexivity | zside | zside | exact Z0].
- apply (chunk_ok_val rsegs _ _ 0x7fff8000 0x42a5 1 (SLit s) s); [reflexivity | cbn; lia | zside | exact Z1].
Qed.
Lemma cl_sh1_is : cl_sh1_region = cl_sh1_region \/ exists s, cl_sh1_region = cl_sh2_region s.
Proof. left. reflexivity. Qed.
Lemma cl_sh2_is : forall s, cl_sh2_region s = cl_sh1_region \/ exists s', cl_sh2_region s = cl_sh2_region s'.
Proof. intros s. right. exists s. reflexivity. Qed.
(* the seqz (hz xor 96000) the second loop leaves for any other hz *)
Lemma cl_lxor_ne : forall hz, hz <> 96000 -> (Z.lxor hz 96000 =? 0) = false.
Proof. intros hz H. apply Z.eqb_neq. intros X. apply (proj1 (Z.lxor_eq_0_iff _ _)) in X. contradiction. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state: the save slot, the four read-only extents and the shadow region sh, each proved from the
   premises the caller has *)
Lemma cl_entry : forall pc ov sh (W : world rsegs) regs memc, 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs lf_extra) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
rdword (aview rsegs (w_H W) memc) 0x9c170 = Some 0xa4f38 ->
rdword (aview rsegs (w_H W) memc) 0xa4f38 = Some SHADOW_OFF ->
val_mem rsegs (mrestrict (w_H W) memc) 0x21520 4 44100 ->
val_mem rsegs (mrestrict (w_H W) memc) (0x21520 + 4) 4 48000 ->
val_mem rsegs (mrestrict (w_H W) memc) (0x21520 + 8) 4 96000 ->
region_ok rsegs (Ereg regs lf_extra) (mrestrict (w_H W) memc) sh ->
(sh = cl_sh1_region \/ exists s, sh = cl_sh2_region s) ->
st_ok rsegs (Ereg regs lf_extra) (ss_cl pc ov sh) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov sh W regs memc Hpc Hov Hpres Hhi Hal Kgot Kcell V0 V1 V2 Hsh Hsc.
rewrite restrict_mkst_fx.
set (E := Ereg regs lf_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 0x7fff8000) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = 0x7fff8000) by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_cl. apply (entry_st_ok_full rsegs); change (Ereg regs lf_extra) with E.
- apply cl_regs_ok. exact Hov.
- destruct Hsc as [-> | (s & ->)]; vm_compute; reflexivity.
- unfold cl_regions, cl_stack_region, cl_got_region, cl_cell_region, cl_tab_region.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [exact Hsh|apply Forall_cons; [|apply Forall_nil]]]]];
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
+ (* closed_list *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
* apply (chunk_ok_val rsegs E _ 0 0x21520 4 (SLit 44100) 44100); [reflexivity | zside | zside | exact V0].
* apply (chunk_ok_val rsegs E _ 0 0x21524 4 (SLit 48000) 48000); [reflexivity | zside | zside | exact V1].
* apply (chunk_ok_val rsegs E _ 0 0x21528 4 (SLit 96000) 96000); [reflexivity | zside | zside | exact V2].
- (* the six extents are pairwise disjoint: sp in [2^46, 2^47] lies above all of them *)
destruct Hsc as [-> | (s & ->)]; apply pairwise_disjoint_of_extents;
unfold cl_regions, cl_stack_region, cl_got_region, cl_cell_region, cl_sh1_region, cl_sh2_region, cl_tab_region,
extent_of_region;
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, U32;
cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [cl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
End b.

(* ---- the walk's plumbing on this file's table ---- *)
(* the write-range obligation: the save slot [sp - 16, sp) lies in the caller's stack allowance *)
Ltac awr_stk :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ]
end end.
(* every write window of a state lies in the save slot [sp - 16, sp) *)
Ltac kwr_stk :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia | lia ] | ]);
destruct Hr.
Ltac cl_run :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok cl_tbl_ok HS HJ SHOK lf_Bspan; [awr_stk | ] end.
Ltac cl_keep :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (lf_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr_stk end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac cl_step := cl_run; cl_keep.
Ltac cl_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok cl_tbl_ok HS SH lf_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the `ret` leaf, into RtPgCSpec's rt_cpost at fx2 = fx, O = True, E = False and R = True: the memory clause
   from KE *)
Ltac cl_leaf :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
eapply (SRr_ret_at rsegs cl_tbl cl_tbl_ok lf_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
unfold rt_cpost, rt_cpost_g; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [exact I|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply lf_same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz _; exact (KE a Ha Hz) | exact I]
end.

(* the entry state with the overrides ov and the shadow region sh, and the env facts the walk reads *)
Ltac cl_setup ov sh Hshok Hsc :=
lazymatch goal with |- SRr _ ?W (mkCfg (mkst ?regs _ ?memc _) _) _ =>
let HS := fresh "HS" in
pose proof (cl_entry A_CHECK_LIST ov sh W regs memc ltac:(unfold A_CHECK_LIST; lia)) as HS;
lazymatch type of HS with ?P -> _ => let HO := fresh "HO" in assert (HO : P); [|specialize (HS HO); clear HO] end;
[ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split;
  [ let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | ]);
  lazymatch goal with |- _ = getr ?r ?n => lazymatch goal with H : getr r n = _ |- _ => rewrite H end end;
  unfold RateCfg.rate_closed; try (match goal with Hr : RateCfg.rate_bit _ = _ |- _ => rewrite Hr end); reflexivity
| ];
specialize (HS ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) Hshok Hsc);
remember (Ereg regs lf_extra) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs lf_extra) E) by (subst E; apply env_agree_refl);
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
assert (E13 : ew E 13 = getr regs 13) by (subst E; exact (ew_Ereg_nat regs _ 13 13%bv eq_refl));
assert (E14 : ew E 14 = getr regs 14) by (subst E; exact (ew_Ereg_nat regs _ 14 14%bv eq_refl));
clear HE;
assert (SHOK : sh_ok rsegs lf_Bx [] E (mrestrict (w_H W) memc)) by constructor;
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity)
end.
Ltac cl_setup2 ov s :=
lazymatch goal with |- SRr _ ?W (mkCfg (mkst ?regs _ ?memc _) _) _ =>
cl_setup ov (cl_sh2_region s) (cl_sh2_ok regs (w_H W) memc s ltac:(lia) ltac:(eassumption) ltac:(eassumption))
  (cl_sh2_is s)
end.

(* the first loop's `beq a0,t2` taken for any other hz: hz = c against hz's case *)
Ltac cl_kill_hz Hb :=
lazymatch goal with E10 : ew ?E 10 = w64 ?hz, Hh : 0 <= ?hz < 2 ^ 64 |- _ =>
exfalso; rewrite branch_eq_U, (U_atom E 10 hz E10 Hh), U_lit in Hb by lia; apply Z.eqb_eq in Hb; lia
end.
(* `bne a2,a0` taken for any other hz: a2 = 0 and a0 = seqz (hz xor 96000) = 0 *)
Ltac cl_kill_xor Hb :=
lazymatch goal with E10 : ew ?E 10 = w64 ?hz, Hh : 0 <= ?hz < 2 ^ 64, N3 : ?hz <> 96000 |- _ =>
exfalso; rewrite branch_ne_U, U_lit, lf_U_sltu1, lf_U_xor_lit, (U_atom E 10 hz E10 Hh) in Hb by lia;
rewrite (cl_lxor_ne hz N3) in Hb; cbn in Hb; discriminate Hb
end.
(* any other hz: the first loop's three compares and the second loop's `bne a2,a0` *)
Ltac cl_other :=
cl_step; let Hb1 := fresh "Hb" in cl_branch Hb1; [cl_kill_hz Hb1 | ];
cl_step; let Hb2 := fresh "Hb" in cl_branch Hb2; [cl_kill_hz Hb2 | ];
cl_step; let Hb3 := fresh "Hb" in cl_branch Hb3; [cl_kill_hz Hb3 | ];
cl_step; let Hb4 := fresh "Hb" in cl_branch Hb4; [cl_kill_xor Hb4 | ].
(* the mask tail, from the state after `bne a2,a0` (or the entry, when both loops are decided): the three bit
   tests on mask and the compare of a4 = rate_best mask on each side *)
Ltac cl_mask_tail :=
lazymatch goal with E13 : ew ?E 13 = w64 ?mask, Hm : 0 <= ?mask < 2 ^ 64,
  E14 : ew ?E 14 = w64 (RateCfg.rate_best ?mask), Hbr : 0 <= RateCfg.rate_best ?mask < 2 ^ 64 |- _ =>
(* stop at 0x83768 bnez a0 (a0 = mask & 4) *)
cl_step; let Hb := fresh "Hb" in cl_branch Hb;
rewrite branch_ne_U, U_and_lit, (U_atom E 13 mask E13 Hm), U_lit, lf_land4, Bool.negb_involutive in Hb by lia;
[ (* bit 2: 0x83790, stop at 0x83798 bne a4,a0 (a0 = 96000) *)
  cl_step; let Hc := fresh "Hc" in cl_branch Hc;
  rewrite branch_ne_U, (U_atom E 14 _ E14 Hbr), U_lit in Hc by lia;
  [ exfalso; rewrite lf_best_bits, Hb in Hc; cbn in Hc; discriminate Hc
  | cl_step; cl_leaf ]
| (* stop at 0x83770 bnez a0 (a0 = mask & 2) *)
  cl_step; let Hc := fresh "Hc" in cl_branch Hc;
  rewrite branch_ne_U, U_and_lit, (U_atom E 13 mask E13 Hm), U_lit, lf_land2, Bool.negb_involutive in Hc by lia;
  [ (* bit 1: 0x837a8, stop at 0x837b0 beq a4,a0 (a0 = 48000) *)
    cl_step; let Hd := fresh "Hd" in cl_branch Hd;
    rewrite branch_eq_U, (U_atom E 14 _ E14 Hbr), U_lit in Hd by lia;
    [ cl_step; cl_leaf
    | exfalso; rewrite lf_best_bits, Hb, Hc in Hd; cbn in Hd; discriminate Hd ]
  | (* 0x83774 .. 0x83784 a0 = (mask << 63 >> 63, arithmetic) & 44100; stop at 0x83788 beq a4,a0 *)
    cl_step; let Hd := fresh "Hd" in cl_branch Hd;
    rewrite branch_eq_U, (U_atom E 14 _ E14 Hbr), lf_U_sext0, (U_atom E 13 mask E13 Hm) in Hd by lia;
    [ cl_step; cl_leaf
    | exfalso; rewrite lf_best_bits, Hb, Hc in Hd; destruct (Z.odd mask); cbn in Hd; discriminate Hd ] ] ]
end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HBgot : as_got_shadow B = 0x9c170.
Hypothesis HBcell : as_shadow_cell B = 0xa4f38.

Theorem rt_check_list_B : rt_check_list_specX rsegs B MT A_CHECK_LIST 0x21520.
Proof using MTL LAWS HBgot HBcell.
unfold rt_check_list_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H11 H12 H14 Htab.
pose proof lf_wx as Hwx. pose proof lf_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_check_STK in Hwlo.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpr : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia).
(* the .got slot and the shadow offset cell by AR's constant law *)
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
(* closed_list's values and its two shadow bytes *)
destruct Htab as (Himg & Hal4 & Hval & Hsh).
assert (V0 : val_mem rsegs (mrestrict (w_H W) memc) 0x21520 4 44100) by exact (Hval 0 ltac:(cbn; lia)).
assert (V1 : val_mem rsegs (mrestrict (w_H W) memc) (0x21520 + 4) 4 48000) by exact (Hval 1 ltac:(cbn; lia)).
assert (V2 : val_mem rsegs (mrestrict (w_H W) memc) (0x21520 + 8) 4 96000) by exact (Hval 2 ltac:(cbn; lia)).
assert (Z0 : val_mem rsegs (mrestrict (w_H W) memc) (0x7fff8000 + 0x42a4) 1 0)
by (refine (cl_zero_byte (w_H W) memc (0x21520 + 7) _ eq_refl _); exact (Hsh (0x21520 + 7) ltac:(cbn; lia))).
destruct (Hsh (0x21520 + 11) ltac:(cbn; lia)) as (s2 & Hs2 & Hok2).
destruct (cl_any_byte _ _ _ _ Hs2) as (Z1 & Hs2r).
change (shadow_of_addr SHADOW_OFF (0x21520 + 11)) with (0x7fff8000 + 0x42a5) in Z1.
assert (Hs2c : s2 = 0 \/ s2 = 4 \/ s2 = 5 \/ s2 = 6 \/ s2 = 7).
{ destruct Hok2 as [-> | [Hl Hh]]; [left; reflexivity|]. change ((0x21520 + 11) mod 8) with 3 in Hl. lia. }
clear Hval Hsh Hs2 Hok2.
(* hz and mask as integers *)
remember (bv_unsigned (getr regs 10)) as hz eqn:Hz0. destruct (lf_atom_of (getr regs 10)) as [H10 Hhz].
rewrite <- Hz0 in H10, Hhz. clear Hz0.
remember (bv_unsigned (getr regs 13)) as mask eqn:Hm0. destruct (lf_atom_of (getr regs 13)) as [H13 Hmask].
rewrite <- Hm0 in H13, Hmask. clear Hm0.
assert (Hbr : 0 <= RateCfg.rate_best mask < 2 ^ 64).
{ destruct (RateCfg.rate_best_range mask) as [-> | [-> | [-> | ->]]];
  unfold RateCfg.RATE_44K1, RateCfg.RATE_48K, RateCfg.RATE_96K; lia. }
unfold cfg_at. change (w64 A_CHECK_LIST) with (Z_to_bv 64 A_CHECK_LIST).
destruct (RateCfg.rate_bit_cases hz) as [[Ehz Rb] | [[Ehz Rb] | [[Ehz Rb] | (N1 & N2 & N3 & Rb)]]];
unfold RateCfg.RATE_44K1, RateCfg.RATE_48K, RateCfg.RATE_96K in *.
- (* hz = 44100: both loops decided (match at index 0), a5 = 1 = a1, a0 = 1 = a2 *)
  subst hz.
  cl_setup [((10%bv : bv 5), SLit 44100); ((11%bv : bv 5), SLit 1); ((12%bv : bv 5), SLit 1)]
    cl_sh1_region (cl_sh1_ok regs (w_H W) memc Z0) cl_sh1_is.
  rewrite H10 in E10; rewrite H13 in E13; rewrite H14 in E14.
  cl_mask_tail.
- (* hz = 48000: both loops decided (match at index 1), a5 = 2 = a1, a0 = 1 = a2 *)
  subst hz.
  cl_setup [((10%bv : bv 5), SLit 48000); ((11%bv : bv 5), SLit 2); ((12%bv : bv 5), SLit 1)]
    cl_sh1_region (cl_sh1_ok regs (w_H W) memc Z0) cl_sh1_is.
  rewrite H10 in E10; rewrite H13 in E13; rewrite H14 in E14.
  cl_mask_tail.
- (* hz = 96000: both loops decided (match at index 2, after the second granule's shadow byte s), a5 = 4 = a1,
     a0 = 1 = a2 *)
  subst hz.
  destruct Hs2c as [-> | [-> | [-> | [-> | ->]]]];
  lazymatch goal with Z1 : val_mem _ _ (_ + 0x42a5) 1 ?s |- _ =>
    cl_setup2 [((10%bv : bv 5), SLit 96000); ((11%bv : bv 5), SLit 4); ((12%bv : bv 5), SLit 1)] s end;
  rewrite H10 in E10; rewrite H13 in E13; rewrite H14 in E14;
  cl_mask_tail.
- (* any other hz: a0 its atom, a1 = 0, a2 = 0 *)
  destruct Hs2c as [-> | [-> | [-> | [-> | ->]]]];
  lazymatch goal with Z1 : val_mem _ _ (_ + 0x42a5) 1 ?s |- _ =>
    cl_setup2 [((11%bv : bv 5), SLit 0); ((12%bv : bv 5), SLit 0)] s end;
  rewrite H10 in E10; rewrite H13 in E13; rewrite H14 in E14;
  cl_other; cl_mask_tail.
Qed.
End c.

Print Assumptions rt_check_list_B.

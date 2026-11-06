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
(* reac_rate_refuse_code, 0x83f60, 92 bytes, 23 words (fuzz_rate.asan, unstripped sha256
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3; the pinned
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a has the same loaded bytes), capstone:
     0x83f60 addi sp,sp,-0x10; 0x83f64 sd ra,8(sp); 0x83f68 addi a1,zero,4; 0x83f6c bgeu a1,a0,0x83f7c;
     0x83f70 auipc a0,0xfff9d; 0x83f74 addi a0,a0,0x690 (a0 = 0x21600); 0x83f78 j 0x83fac;
     0x83f7c auipc a1,0x18; 0x83f80 ld a1,-0x10c(a1) (the 8 bytes at the .got slot 0x9be70: 0xa4c38);
     0x83f84 slli a0,a0,3; 0x83f88 ld a1,0(a1) (the 8 bytes at 0xa4c38, the runtime's shadow offset cell: 0x7fff8000);
     0x83f8c auipc a2,0x18; 0x83f90 addi a2,a2,-0x30c (a2 = 0x9bc80, the 40-byte table codes[5]);
     0x83f94 add a0,a2,a0; 0x83f98 srli a2,a0,3; 0x83f9c add a1,a2,a1 (the shadow byte's address
     ((0x9bc80 + 8 r) >> 3) + 0x7fff8000); 0x83fa0 lbu a1,0(a1) and 0x83fa4 bnez a1,0x83fb8 (the instrumented
     check); 0x83fa8 ld a0,0(a0) (codes[r]); 0x83fac ld ra,8(sp); 0x83fb0 addi sp,sp,0x10; 0x83fb4 ret;
     0x83fb8 jal (the error path of an 8-byte load).
   r is the 64-bit word in a0 at entry. The only store is `sd ra,8(sp)` into the 16-byte save slot [sp - 16, sp)
   (awr_stk: inside the caller's stack window by the contract's window premises); every other byte is only read.
   r >= 5: the entry state holds a0 as its atom; the engine stops at the bgeu, which is split (branch_geu_U): the
   taken side needs r <= 4 and is refuted, the other side forms 0x21600 and runs to the `ret`.
   r = 0 .. 4: the entry state holds a0 as the literal r (regs_ok_override), so the engine takes the bgeu, forms
   every address as a literal and reads four read-only extents beside the save slot: the .got slot [0x9be70, 0x9be78)
   (0xa4c38, by AR's constant law and the record's as_got_shadow), the shadow offset cell [0xa4c38, 0xa4c40) (env
   slot 32 = 0x7fff8000, by the same law and as_shadow_cell), the five shadow bytes of the table at offsets 0x13790 ..
   0x13794 from slot 32 (each 0: the table's 40 bytes are addressable, rt_u64tab, and each of its five 8-byte
   granules is fully addressable), and the table [0x9bc80, 0x9bca8) (codes[0 .. 4] = 0x21600, 0x21620, 0x21640,
   0x21660, 0x21680, rt_u64tab's values).
   WHY THE ERROR PATH IS UNREACHABLE: the shadow byte the `lbu` reads is the literal 0, so the engine decides the
   `bnez` at 0x83fa4 as not taken; one run reaches the `ret` and the jal at 0x83fb8 is never stepped. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgCheck.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- the image: the function's 23 words, the table the engine reads its code from ---- *)
Definition A_REFUSE : Z := 0x83f60.
Definition rf_tbl : ctable := build_table rsegs A_REFUSE 23 TEmpty.
Lemma rf_tbl_ok : table_ok rsegs rf_tbl.
Proof. apply build_table_ok0. unfold A_REFUSE. lia. Qed.
(* the table reac_rate_refuse_code.codes (0x9bc80, .data.rel.ro) and its five values, the address of codes[0]'s text
   that the r >= 5 path forms (0x21600), the .got slot of the shadow offset cell (0x9be70) and that cell
   (__asan_shadow_memory_dynamic_address 0xa4c38), measured on the image *)
Definition RF_TBL : Z := 0x9bc80.
Definition RF_CS : list Z := [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Definition RF_COV : Z := 0x21600.

(* ---- the read-only extents of the table path (base None: absolute addresses; base Some 32: offsets from
   env slot 32 = 0x7fff8000) [knock lib/A/ACeh.v got_region / bcell_region] ---- *)
(* the .got slot [0x9be70, 0x9be78): the address of the shadow offset cell *)
Definition rf_got_region : YP09.region :=
YP09.mkRegion None 0x9be70 0x9be78 0 0 [YP09.mkChunk 0x9be70 (CVal 8 (SLit 0xa4c38))].
(* the shadow offset cell [0xa4c38, 0xa4c40): 0x7fff8000, the atom of env slot 32 *)
Definition rf_cell_region : YP09.region :=
YP09.mkRegion None 0xa4c38 0xa4c40 0 0 [YP09.mkChunk 0xa4c38 (CVal 8 (SOff 32 0))].
(* the five shadow bytes of the table, (0x9bc80 >> 3) + 0x7fff8000 = 0x13790 + 0x7fff8000 and the next four: all 0 *)
Definition rf_sh_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0x13790 0x13795 0 0
[YP09.mkChunk 0x13790 (CVal 1 (SLit 0)); YP09.mkChunk 0x13791 (CVal 1 (SLit 0)); YP09.mkChunk 0x13792 (CVal 1 (SLit 0));
 YP09.mkChunk 0x13793 (CVal 1 (SLit 0)); YP09.mkChunk 0x13794 (CVal 1 (SLit 0))].
(* the table [0x9bc80, 0x9bca8): codes[0 .. 4] *)
Definition rf_tbl_region : YP09.region :=
YP09.mkRegion None 0x9bc80 0x9bca8 0 0
[YP09.mkChunk 0x9bc80 (CVal 8 (SLit 0x21600)); YP09.mkChunk 0x9bc88 (CVal 8 (SLit 0x21620));
 YP09.mkChunk 0x9bc90 (CVal 8 (SLit 0x21640)); YP09.mkChunk 0x9bc98 (CVal 8 (SLit 0x21660));
 YP09.mkChunk 0x9bca0 (CVal 8 (SLit 0x21680))].
Definition rf_regions : smem := [ ck_stack_region 16; rf_got_region; rf_cell_region; rf_sh_region; rf_tbl_region ].
Definition ss_rf (pc : Z) (ov : list (bv 5 * sv)) : sstate := mkSS pc (ck_sr ov) rf_regions None ck_facts.

(* a shadow byte s of an address x with x mod 8 = 7 that range_addressable accepts is 0 *)
Lemma rf_zero_byte : forall H mem x a, x mod 8 = 7 ->
(exists s, aview rsegs H mem a = Some s /\ saddr_ok x s) -> val_mem rsegs (mrestrict H mem) a 1 0.
Proof.
intros H mem x a Hx (s & Hs & Hok).
destruct Hok as [-> | [H1 H2]]; [|lia].
apply aview_byte in Hs as (b & Hb & Hv & _).
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite <- Hv. first [reflexivity | vm_compute; reflexivity].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state of the table path: ck_entry's save slot, sp facts and registers, and the four read-only
   extents, each proved from the premises the caller has (the table's from rt_u64tab) *)
Lemma rf_entry : forall pc ov (W : world rsegs) regs memc, 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs ck_extra) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
rdword (aview rsegs (w_H W) memc) 0x9be70 = Some 0xa4c38 ->
rdword (aview rsegs (w_H W) memc) 0xa4c38 = Some SHADOW_OFF ->
rt_u64tab rsegs (w_H W) memc RF_TBL RF_CS ->
st_ok rsegs (Ereg regs ck_extra) (ss_rf pc ov) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov W regs memc Hpc Hov Hpres Hhi Hal Kgot Kcell (_ & _ & _ & Hv & Hsh).
assert (V0 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bc80 8 0x21600)
by exact (Hv 0 ltac:(unfold RF_CS; simpl; lia)).
assert (V1 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bc88 8 0x21620)
by exact (Hv 1 ltac:(unfold RF_CS; simpl; lia)).
assert (V2 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bc90 8 0x21640)
by exact (Hv 2 ltac:(unfold RF_CS; simpl; lia)).
assert (V3 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bc98 8 0x21660)
by exact (Hv 3 ltac:(unfold RF_CS; simpl; lia)).
assert (V4 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bca0 8 0x21680)
by exact (Hv 4 ltac:(unfold RF_CS; simpl; lia)).
clear Hv.
assert (Hsh' : forall x, 0x9bc80 <= x < 0x9bc80 + 40 ->
exists s, aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x) = Some s /\ saddr_ok x s)
by (intros x Hx; exact (Hsh x ltac:(unfold RF_TBL, RF_CS; simpl; lia))).
clear Hsh.
rewrite restrict_mkst_fx.
set (E := Ereg regs ck_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 0x7fff8000) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = 0x7fff8000) by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_rf. apply (entry_st_ok_full rsegs); change (Ereg regs ck_extra) with E.
- apply ck_regs_ok. exact Hov.
- vm_compute. reflexivity.
- unfold rf_regions, ck_stack_region, rf_got_region, rf_cell_region, rf_sh_region, rf_tbl_region.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ (* the save slot *)
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
+ (* the .got slot *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 0x9be70 8 (SLit 0xa4c38) 0xa4c38); [reflexivity | zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgot).
+ (* the shadow offset cell *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 0xa4c38 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcell).
+ (* the five shadow bytes of the table: each granule [0x9bc80 + 8 i, 0x9bc80 + 8 i + 8) is fully addressable, so
     each byte is 0 (rf_zero_byte at its last byte) *)
rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x13790 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bc80 + 7) _ eq_refl _).
exact (Hsh' (0x9bc80 + 7) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x13791 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bc80 + 15) _ eq_refl _).
exact (Hsh' (0x9bc80 + 15) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x13792 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bc80 + 23) _ eq_refl _).
exact (Hsh' (0x9bc80 + 23) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x13793 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bc80 + 31) _ eq_refl _).
exact (Hsh' (0x9bc80 + 31) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x13794 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bc80 + 39) _ eq_refl _).
exact (Hsh' (0x9bc80 + 39) ltac:(lia)).
+ (* the table *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
* apply (chunk_ok_val rsegs E _ 0 0x9bc80 8 (SLit 0x21600) 0x21600); [reflexivity | zside | zside | exact V0].
* apply (chunk_ok_val rsegs E _ 0 0x9bc88 8 (SLit 0x21620) 0x21620); [reflexivity | zside | zside | exact V1].
* apply (chunk_ok_val rsegs E _ 0 0x9bc90 8 (SLit 0x21640) 0x21640); [reflexivity | zside | zside | exact V2].
* apply (chunk_ok_val rsegs E _ 0 0x9bc98 8 (SLit 0x21660) 0x21660); [reflexivity | zside | zside | exact V3].
* apply (chunk_ok_val rsegs E _ 0 0x9bca0 8 (SLit 0x21680) 0x21680); [reflexivity | zside | zside | exact V4].
- (* the six extents are pairwise disjoint: sp in [2^46, 2^47] lies above all of them *)
apply pairwise_disjoint_of_extents.
unfold rf_regions, ck_stack_region, rf_got_region, rf_cell_region, rf_sh_region, rf_tbl_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [ck_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
End b.

(* ---- the walk's plumbing on this file's table [RPgCheck.v ck_run / ck_leaf, RPgCfgChanges.v cfg_branch /
   cfg_r10 / cfg_leaf] ---- *)
Ltac rf_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok rf_tbl_ok HS HJ SHOK ck_Bspan; [awr | ] end.
Ltac rf_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok rf_tbl_ok HS SH ck_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac rf_r10 R10 :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
assert (R10 : getr (ms_regs ms) (10%bv : bv 5) = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms (10%bv : bv 5) HS)
end.
(* the `ret` leaf, into RtPgCSpec's rt_cpost at fx2 = fx, E = False: the memory clause from KE, vtac the clause on
   a0 from R10 *)
Ltac rf_leaf vtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in rf_r10 R10;
eapply (SRr_ret_at rsegs rf_tbl rf_tbl_ok ck_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
cbv beta delta [rt_cpost rt_cpost_g]; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [exact I|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_ck]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz _; exact (KE a Ha Hz) | cbv beta; rewrite R10; vtac]
end.
(* the env facts after the entry state is posed as HS [RPgCheck.v ck_start] *)
Ltac rf_env :=
lazymatch goal with HS : st_ok _ (Ereg ?regs ck_extra) _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W ?memc _ _ |- _ =>
remember (Ereg regs ck_extra) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs ck_extra) E) by (subst E; apply env_agree_refl);
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
clear HE;
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) memc)) by constructor;
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity)
end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the image record's .got slot of the shadow offset cell and that cell (image A: 0x9be70 holds 0xa4c38,
   __asan_shadow_memory_dynamic_address); the image's symbol record gives both *)
Hypothesis HBgot : as_got_shadow B = 0x9be70.
Hypothesis HBcell : as_shadow_cell B = 0xa4c38.

Theorem rt_refuse_code_A : rt_refuse_code_specX rsegs B MT 0x83f60 RF_TBL RF_COV RF_CS.
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
- (* r >= 5: a0 is its atom; the engine stops at 0x83f6c bgeu a1,a0 (a1 = 4) *)
pose proof (ck_entry A_REFUSE [] W regs memc ltac:(unfold A_REFUSE; lia) (Forall_nil _) Hpr Hsp Hal16) as HS.
rf_env.
rewrite H10 in E10.
rf_run awr_stk. ck_keep kwr_stk.
rf_branch Hb.
+ (* taken: 4 >= r (unsigned), against r >= 5 *)
exfalso. rewrite branch_geu_U in Hb. rewrite (U_lit E 4) in Hb by lia. rewrite (U_atom E 10 r E10 Hr64) in Hb.
destruct (Z.ltb_spec 4 r); cbn in Hb; [discriminate Hb | lia].
+ (* not taken: 0x83f70 auipc / 0x83f74 addi form 0x21600, 0x83f78 j 0x83fac; stop at 0x83fb4 ret *)
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
(* 0x83f60 .. 0x83fb0: the bgeu taken (4 >= r), every address a literal, the shadow byte the literal 0 so the
   bnez not taken (the error path at 0x83fb8 is never stepped), a0 = codes[r]; stop at 0x83fb4 ret *)
destruct Hr04 as [-> | [-> | [-> | [-> | ->]]]].
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
Qed.
End c.

Print Assumptions rt_refuse_code_A.

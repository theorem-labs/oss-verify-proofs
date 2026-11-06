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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgRefuse.v at b908b1be5a37, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; image A's walk of reac_rate_refuse_code (rt_refuse_code_A, Section c) and its listing comment are left out: image B's refuse_code is other code (27 words), walked elsewhere; the Modified-by lines above describe how lib/A/RtPgRefuse.v was made and quote that file's image-A values; the code below carries image B's values. *)
(* Image B's (fuzz_rate.asan-ubsan, unstripped sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1;
   the pinned c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14 has the same loaded bytes) parts of the
   table path of reac_rate_refuse_code that other walks reuse: the function's address and code table (0x841b4, 108
   bytes, 27 words), the table reac_rate_refuse_code.codes [0x9bf80, 0x9bfa8) (codes[0 .. 4] = 0x21600, 0x21620,
   0x21640, 0x21660, 0x21680, the same pointers as image A's), the .got slot [0x9c170, 0x9c178) of the shadow offset
   cell [0xa4f38, 0xa4f40), the five shadow bytes of the table at offsets 0x137f0 .. 0x137f4 from env slot 32, their
   read-only regions, the entry state rf_entry, and the run / branch / leaf tactics. Image A's walk of the function
   is not here: image B's reac_rate_refuse_code is other code than image A's 23 words, so its walk is its own file. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ---- the image: the function's 27 words, the table the engine reads its code from ---- *)
Definition A_REFUSE : Z := 0x841b4.
Definition rf_tbl : ctable := build_table rsegs A_REFUSE 27 TEmpty.
Lemma rf_tbl_ok : table_ok rsegs rf_tbl.
Proof. apply build_table_ok0. unfold A_REFUSE. lia. Qed.
(* the table reac_rate_refuse_code.codes (0x9bf80, .data.rel.ro) and its five values, the address of codes[0]'s text
   that the r >= 5 path forms (0x21600), the .got slot of the shadow offset cell (0x9c170) and that cell
   (__asan_shadow_memory_dynamic_address 0xa4f38), measured on the image *)
Definition RF_TBL : Z := 0x9bf80.
Definition RF_CS : list Z := [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Definition RF_COV : Z := 0x21600.

(* ---- the read-only extents of the table path (base None: absolute addresses; base Some 32: offsets from
   env slot 32 = 0x7fff8000) [knock lib/A/ACeh.v got_region / bcell_region] ---- *)
(* the .got slot [0x9c170, 0x9c178): the address of the shadow offset cell *)
Definition rf_got_region : YP09.region :=
YP09.mkRegion None 0x9c170 0x9c178 0 0 [YP09.mkChunk 0x9c170 (CVal 8 (SLit 0xa4f38))].
(* the shadow offset cell [0xa4f38, 0xa4f40): 0x7fff8000, the atom of env slot 32 *)
Definition rf_cell_region : YP09.region :=
YP09.mkRegion None 0xa4f38 0xa4f40 0 0 [YP09.mkChunk 0xa4f38 (CVal 8 (SOff 32 0))].
(* the five shadow bytes of the table, (0x9bf80 >> 3) + 0x7fff8000 = 0x137f0 + 0x7fff8000 and the next four: all 0 *)
Definition rf_sh_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0x137f0 0x137f5 0 0
[YP09.mkChunk 0x137f0 (CVal 1 (SLit 0)); YP09.mkChunk 0x137f1 (CVal 1 (SLit 0)); YP09.mkChunk 0x137f2 (CVal 1 (SLit 0));
 YP09.mkChunk 0x137f3 (CVal 1 (SLit 0)); YP09.mkChunk 0x137f4 (CVal 1 (SLit 0))].
(* the table [0x9bf80, 0x9bfa8): codes[0 .. 4] *)
Definition rf_tbl_region : YP09.region :=
YP09.mkRegion None 0x9bf80 0x9bfa8 0 0
[YP09.mkChunk 0x9bf80 (CVal 8 (SLit 0x21600)); YP09.mkChunk 0x9bf88 (CVal 8 (SLit 0x21620));
 YP09.mkChunk 0x9bf90 (CVal 8 (SLit 0x21640)); YP09.mkChunk 0x9bf98 (CVal 8 (SLit 0x21660));
 YP09.mkChunk 0x9bfa0 (CVal 8 (SLit 0x21680))].
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
rdword (aview rsegs (w_H W) memc) 0x9c170 = Some 0xa4f38 ->
rdword (aview rsegs (w_H W) memc) 0xa4f38 = Some SHADOW_OFF ->
rt_u64tab rsegs (w_H W) memc RF_TBL RF_CS ->
st_ok rsegs (Ereg regs ck_extra) (ss_rf pc ov) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov W regs memc Hpc Hov Hpres Hhi Hal Kgot Kcell (_ & _ & _ & Hv & Hsh).
assert (V0 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf80 8 0x21600)
by exact (Hv 0 ltac:(unfold RF_CS; simpl; lia)).
assert (V1 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf88 8 0x21620)
by exact (Hv 1 ltac:(unfold RF_CS; simpl; lia)).
assert (V2 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf90 8 0x21640)
by exact (Hv 2 ltac:(unfold RF_CS; simpl; lia)).
assert (V3 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bf98 8 0x21660)
by exact (Hv 3 ltac:(unfold RF_CS; simpl; lia)).
assert (V4 : val_mem rsegs (mrestrict (w_H W) memc) 0x9bfa0 8 0x21680)
by exact (Hv 4 ltac:(unfold RF_CS; simpl; lia)).
clear Hv.
assert (Hsh' : forall x, 0x9bf80 <= x < 0x9bf80 + 40 ->
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
apply (chunk_ok_val rsegs E _ 0 0x9c170 8 (SLit 0xa4f38) 0xa4f38); [reflexivity | zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgot).
+ (* the shadow offset cell *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 0xa4f38 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcell).
+ (* the five shadow bytes of the table: each granule [0x9bf80 + 8 i, 0x9bf80 + 8 i + 8) is fully addressable, so
     each byte is 0 (rf_zero_byte at its last byte) *)
rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137f0 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf80 + 7) _ eq_refl _).
exact (Hsh' (0x9bf80 + 7) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137f1 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf80 + 15) _ eq_refl _).
exact (Hsh' (0x9bf80 + 15) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137f2 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf80 + 23) _ eq_refl _).
exact (Hsh' (0x9bf80 + 23) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137f3 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf80 + 31) _ eq_refl _).
exact (Hsh' (0x9bf80 + 31) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x137f4 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9bf80 + 39) _ eq_refl _).
exact (Hsh' (0x9bf80 + 39) ltac:(lia)).
+ (* the table *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
* apply (chunk_ok_val rsegs E _ 0 0x9bf80 8 (SLit 0x21600) 0x21600); [reflexivity | zside | zside | exact V0].
* apply (chunk_ok_val rsegs E _ 0 0x9bf88 8 (SLit 0x21620) 0x21620); [reflexivity | zside | zside | exact V1].
* apply (chunk_ok_val rsegs E _ 0 0x9bf90 8 (SLit 0x21640) 0x21640); [reflexivity | zside | zside | exact V2].
* apply (chunk_ok_val rsegs E _ 0 0x9bf98 8 (SLit 0x21660) 0x21660); [reflexivity | zside | zside | exact V3].
* apply (chunk_ok_val rsegs E _ 0 0x9bfa0 8 (SLit 0x21680) 0x21680); [reflexivity | zside | zside | exact V4].
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

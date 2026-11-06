(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/RPgCheck.v at fb6520a9cda (its entry state, save-slot region, run / keep / leaf chain and write obligations, reused by Require) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_refuse_code 0x82e6c against lib/A/RPgCSpec.v's rl_refuse_code_specX on the concrete image lib/A/Img0.v rsegs, with its own code table (23 words from 0x82e6c), the a0 clause of lib/A/RPgCfgChanges.v's cfg_leaf and its cfg_branch split, and the .got-slot / shadow-offset-cell regions of proofs/libreac/fuzz_knock/lib/A/ACeh.v got_region / bcell_region at origin/ossv/recipes 6ebe35ba632 (with lib/A/APgRt.v's al_const / chunk_ok_val / val_mem_of_rdword proofs of them); new: the regions of the two shadow bytes of the table and of the table itself, and the split on a0 (r >= 2: one branch; r = 0, r = 1: a0 a literal). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgRefuse.v at 80fff82b3d8 for reac-pw/fuzz_role's asan-ubsan image (fuzz_role.asan-ubsan), by hand, with the image-B form of proofs/reac-pw/fuzz_rate/lib/AU/RtPgRefuseB.v at 7e78c83a433 as the template: the image is lib/AU/Img0.v rsegs and the check kit lib/AU/RPgCheck.v; the code table is 27 words; the .got slot, the shadow offset cell, the table, its two shadow bytes and the literal of the r >= 2 path are image B's; B's code forms the table's address before it reads the shadow offset cell and has one more branch, the pointer-overflow trap 0x830c8, decided on literals; the top rl_refuse_code_A -> rl_refuse_code_B; the record hypotheses name B's .got slot 0x9aad0 and shadow offset cell 0xa3678. *)
(* reac_role_refuse_code, 0x8309c, 108 bytes, 27 words (fuzz_role.asan-ubsan, unstripped sha256
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a; the pinned
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0 has the same bytes):
     0x8309c addi sp,sp,-0x10; 0x830a0 sd ra,8(sp); 0x830a4 addi a1,zero,1; 0x830a8 bgeu a1,a0,0x830b8;
     0x830ac auipc a0,0xfff9e; 0x830b0 addi a0,a0,0x494 (a0 = 0x21540); 0x830b4 j 0x830f4;
     0x830b8 slli a2,a0,3; 0x830bc auipc a1,0x18; 0x830c0 addi a1,a1,-0x79c (a1 = 0x9a920, the 16-byte table codes[2]);
     0x830c4 xori a3,a1,-1 (`not`); 0x830c8 bltu a3,a2,0x83100 (the trap branch: 0x9a920 + 8 r would wrap);
     0x830cc auipc a2,0x18; 0x830d0 ld a2,-0x5fc(a2) (the 8 bytes at the .got slot 0x9aad0: 0xa3678);
     0x830d4 ld a2,0(a2) (the 8 bytes at 0xa3678, the runtime's shadow offset cell: 0x7fff8000);
     0x830d8 slli a0,a0,3; 0x830dc add a0,a1,a0; 0x830e0 srli a1,a0,3; 0x830e4 add a1,a1,a2 (the shadow byte's address
     ((0x9a920 + 8 r) >> 3) + 0x7fff8000); 0x830e8 lbu a1,0(a1) and 0x830ec bnez a1,0x83104 (the instrumented
     check); 0x830f0 ld a0,0(a0) (codes[r]); 0x830f4 ld ra,8(sp); 0x830f8 addi sp,sp,0x10; 0x830fc ret;
     0x83100 unimp (the trap); 0x83104 jal (the error path of an 8-byte load).
   The table reac_role_refuse_code.codes is 0x9a920 in .data.rel.ro (A 0x9a680); its two words are 0x21540 ("none")
   and 0x21560 ("malformed"), the r >= 2 literal 0x21540 ("none"). r is the 64-bit word in a0 at entry. The only
   store is `sd ra,8(sp)` into the 16-byte save slot [sp - 16, sp) (awr_stk: inside the caller's stack window by the
   contract's window premises); every other byte is only read.
   r >= 2: the entry state holds a0 as its atom; the engine stops at the bgeu, which is split (branch_geu_U): the
   taken side needs r <= 1 and is refuted, the other side forms 0x21540 and runs to the `ret`.
   r = 0 and r = 1: the entry state holds a0 as the literal r (regs_ok_override), so the engine takes the bgeu
   and forms every value as a literal: a2 = 8 r, a1 = 0x9a920, a3 = 2^64 - 1 - 0x9a920. THE TRAP BRANCH IS NOT
   TAKEN: `bltu a3,a2` compares two literals, and 8 r <= 8 < 2^64 - 1 - 0x9a920, so the engine decides it not taken
   and the `unimp` at 0x83100 is never stepped. It then reads five read-only extents beside the save slot: the .got
   slot [0x9aad0, 0x9aad8) (0xa3678, by AR's constant law and the record's as_got_shadow), the shadow offset cell
   [0xa3678, 0xa3680) (env slot 32 = 0x7fff8000, by the same law and as_shadow_cell), the two shadow bytes of the
   table at offsets 0x13524 and 0x13525 from slot 32 (each 0: the table's 16 bytes are addressable and each of
   its two 8-byte granules is fully addressable), and the table [0x9a920, 0x9a930) (codes[0] = 0x21540, codes[1]
   = 0x21560, the contract's val_mem premises).
   WHY THE ERROR PATH IS UNREACHABLE: the shadow byte the `lbu` reads is the literal 0, so the engine decides the
   `bnez` at 0x830ec as not taken; one run reaches the `ret` and the jal at 0x83104 is never stepped. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCheck.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image: the function's 27 words, the table the engine reads its code from ---- *)
Definition A_REFUSE : Z := 0x8309c.
Definition rf_tbl : ctable := build_table rsegs A_REFUSE 27 TEmpty.
Lemma rf_tbl_ok : table_ok rsegs rf_tbl.
Proof. apply build_table_ok0. unfold A_REFUSE. lia. Qed.

(* ---- the read-only extents of the table path (base None: absolute addresses; base Some 32: offsets from
   env slot 32 = 0x7fff8000) [knock lib/A/ACeh.v got_region / bcell_region] ---- *)
(* the .got slot [0x9aad0, 0x9aad8): the address of the shadow offset cell *)
Definition rf_got_region : YP09.region :=
YP09.mkRegion None 0x9aad0 0x9aad8 0 0 [YP09.mkChunk 0x9aad0 (CVal 8 (SLit 0xa3678))].
(* the shadow offset cell [0xa3678, 0xa3680): 0x7fff8000, the atom of env slot 32 *)
Definition rf_cell_region : YP09.region :=
YP09.mkRegion None 0xa3678 0xa3680 0 0 [YP09.mkChunk 0xa3678 (CVal 8 (SOff 32 0))].
(* the two shadow bytes of the table, (0x9a920 >> 3) + 0x7fff8000 and the next one: both 0 *)
Definition rf_sh_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0x13524 0x13526 0 0
[YP09.mkChunk 0x13524 (CVal 1 (SLit 0)); YP09.mkChunk 0x13525 (CVal 1 (SLit 0))].
(* the table [0x9a920, 0x9a930): codes[0] = 0x21540, codes[1] = 0x21560 *)
Definition rf_tbl_region : YP09.region :=
YP09.mkRegion None 0x9a920 0x9a930 0 0
[YP09.mkChunk 0x9a920 (CVal 8 (SLit 0x21540)); YP09.mkChunk 0x9a928 (CVal 8 (SLit 0x21560))].
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
   extents, each proved from the premises the caller has *)
Lemma rf_entry : forall pc ov (W : world rsegs) regs memc, 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs ck_extra) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
rdword (aview rsegs (w_H W) memc) 0x9aad0 = Some 0xa3678 ->
rdword (aview rsegs (w_H W) memc) 0xa3678 = Some SHADOW_OFF ->
val_mem rsegs (mrestrict (w_H W) memc) 0x9a920 8 0x21540 ->
val_mem rsegs (mrestrict (w_H W) memc) (0x9a920 + 8) 8 0x21560 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF 0x9a920 16 ->
st_ok rsegs (Ereg regs ck_extra) (ss_rf pc ov) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov W regs memc Hpc Hov Hpres Hhi Hal Kgot Kcell V0 V1 Hsh.
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
apply (chunk_ok_val rsegs E _ 0 0x9aad0 8 (SLit 0xa3678) 0xa3678); [reflexivity | zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgot).
+ (* the shadow offset cell *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 0xa3678 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcell).
+ (* the two shadow bytes of the table: the granules [0x9a920, 0x9a928) and [0x9a928, 0x9a930) are fully
     addressable, so each byte is 0 (rf_zero_byte at their last bytes) *)
rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x13524 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9a920 + 7) _ eq_refl _).
exact (Hsh (0x9a920 + 7) ltac:(lia)).
* apply (chunk_ok_val rsegs E _ 0x7fff8000 0x13525 1 (SLit 0) 0); [reflexivity | zside | zside |].
refine (rf_zero_byte (w_H W) memc (0x9a920 + 15) _ eq_refl _).
exact (Hsh (0x9a920 + 15) ltac:(lia)).
+ (* the table *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val rsegs E _ 0 0x9a920 8 (SLit 0x21540) 0x21540); [reflexivity | zside | zside | exact V0].
* apply (chunk_ok_val rsegs E _ 0 0x9a928 8 (SLit 0x21560) 0x21560); [reflexivity | zside | zside | exact V1].
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
(* the `ret` leaf, into RPgCSpec's rl_post at fx2 = fx, E = False: the memory clause from KE, vtac the clause on
   a0 from R10 *)
Ltac rf_leaf vtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in rf_r10 R10;
eapply (SRr_ret_at rsegs rf_tbl rf_tbl_ok ck_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
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
(* the image record's .got slot of the shadow offset cell and that cell (image B: 0x9aad0 holds 0xa3678, the
   runtime's shadow offset cell __asan_shadow_memory_dynamic_address); the image's symbol record gives both *)
Hypothesis HBgot : as_got_shadow B = 0x9aad0.
Hypothesis HBcell : as_shadow_cell B = 0xa3678.

Theorem rl_refuse_code_B : rl_refuse_code_specX rsegs B MT 0x8309c 0x9a920 0x21540 0x21560 0x21540.
Proof using MTL LAWS HBgot HBcell.
change (rl_refuse_code_specX rsegs B MT A_REFUSE 0x9a920 0x21540 0x21560 0x21540).
unfold rl_refuse_code_specX, rl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) Hc0 Hc1 Hcov Himg V0 V1 Hsh.
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
destruct (Z.le_gt_cases 2 r) as [Hge | Hlt].
- (* r >= 2: a0 is its atom; the engine stops at 0x830a8 bgeu a1,a0 (a1 = 1) *)
pose proof (ck_entry A_REFUSE [] W regs memc ltac:(unfold A_REFUSE; lia) (Forall_nil _) Hpr Hsp Hal16) as HS.
rf_env.
rewrite H10 in E10.
rf_run awr_stk. ck_keep kwr_stk.
rf_branch Hb.
+ (* taken: 1 >= r (unsigned), against r >= 2 *)
exfalso. rewrite branch_geu_U in Hb. rewrite (U_lit E 1) in Hb by lia. rewrite (U_atom E 10 r E10 Hr64) in Hb.
destruct (Z.ltb_spec 1 r); cbn in Hb; [discriminate Hb | lia].
+ (* not taken: 0x830ac auipc / 0x830b0 addi form 0x21540, 0x830b4 j 0x830f4; stop at 0x830fc ret *)
rf_run awr_stk. ck_keep kwr_stk.
rf_leaf ltac:(unfold rl_refuse; destruct (Z.eqb_spec r 0); [lia|]; destruct (Z.eqb_spec r 1); [lia|]; reflexivity).
- (* r = 0 or r = 1: a0 is the literal r; the .got slot and the shadow offset cell by AR's constant law *)
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (rf_entry A_REFUSE [((10%bv : bv 5), SLit r)] W regs memc ltac:(unfold A_REFUSE; lia)) as HS.
lazymatch type of HS with ?P -> _ => assert (HO : P); [|specialize (HS HO); clear HO] end.
{ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite ck_lit. symmetry. exact H10. }
specialize (HS Hpr Hsp Hal16 Kgot Kcell V0 V1 Hsh).
rf_env.
assert (Hr01 : r = 0 \/ r = 1) by lia.
(* 0x8309c .. 0x830f8: the bgeu taken (1 >= r); 0x830b8 slli a2 / 0x830bc auipc / 0x830c0 addi / 0x830c4 not and the
   trap branch 0x830c8 bltu a3,a2 on the literals 2^64 - 1 - 0x9a920 and 8 r, not taken (the unimp at 0x83100 is never
   stepped); every address a literal, the shadow byte the literal 0 so the bnez 0x830ec not taken (the error path at
   0x83104 is never stepped), a0 = codes[r]; stop at 0x830fc ret *)
destruct Hr01 as [-> | ->].
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
+ rf_run awr_stk. ck_keep kwr_stk. rf_leaf ltac:(first [reflexivity | vm_compute; reflexivity]).
Qed.
End c.

Print Assumptions rl_refuse_code_B.
About rl_refuse_code_B.

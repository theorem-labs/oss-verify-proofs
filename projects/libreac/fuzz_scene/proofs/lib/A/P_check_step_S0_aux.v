(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACk0.v (lines 598-701) to libreac/fuzz_scene's asan walk. *)
(* Helper for P_check_step_S0.v (segment S0 of the ASan walk of check_step in fuzz_scene.asan, 0x8319c .. 0x832fc):
   the symbolic state at check_step's entry and the lemma that the entry facts (afn_pre with the cut's
   TCHECK_STEP_STK, sp 32-aligned) give it. Port of cgif_file_fuzzer A/ACk0.v:598-701 (ng_entryX).

   The state: atoms 0..31 are the entry registers, atom 32 the shadow base SB; the regions are the entry stack
   window below sp (the 128-byte own frame, `addi sp,sp,-0x80` 0x8319c), the shadow-base GOT word (object 1) with the
   shadow-base cell (object 16), and the use-after-return flag's GOT word (object 0) with the flag cell
   (object 17 = as_uar_cell B, PALib), which holds 1 in every AR state (al_const). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneFrame YC1g YC1h YC81 SceneACjr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition cs_extra : list word := [Z_to_bv 64 SB].
Definition cs_regions0 : smem :=
[ stack_region 128; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 17); uar_cell_regionP (A_OBJ 17) ].
Definition cs_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF SB SB 0) ].
Definition ss_cs0 : sstate := mkSS AF_check_step sr_atoms cs_regions0 None (mkFacts cs_atoms0 [] []).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* A saved-register slot of the stack region (atom 2) gives the rdword at sp + od in the reader view. *)
Lemma cs_slot : forall E H mem lo hi wlo whi cs sp od (n : nat) (r : bv 5) (regs : bvmap 5 word),
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp ->
In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs -> ew E n = getr regs r ->
rdword (aview SEGS H mem) (sp + od) = Some (bv_unsigned (getr regs r)).
Proof.
intros E H mem lo hi wlo whi cs sp od n r regs HR Hsp Hin Hn.
pose proof (bv_unsigned_in_range _ (getr regs r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply rdword_of_val_mem; [| exact Hr].
eapply (slot_of_region E _ sp cs lo hi wlo whi od (SOff n 0) _ HR Hsp Hin); [| exact Hr].
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Lemma cs_entry : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B TCHECK_STEP_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs cs_extra)) ss_cs0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_step)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE Hal32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kguar, Kuar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs cs_extra)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs cs_extra 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E257 : ew E (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E258 : ew E (A_OBJ 17) = Z_to_bv 64 (VAL (A_OBJ 17))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 16 ltac:(lia)) as Hob16. pose proof (pa_obj_img 17 ltac:(lia)) as Hob17.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_cs0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cs_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FFS. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
[cbn [sv_denot]; rewrite E257, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) E257) by (pose proof (pa_val_range (A_OBJ 16)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 17) 0) (VAL (A_OBJ 17)));
[cbn [sv_denot]; rewrite E258, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 17)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB (A_OBJ 17) (VAL (A_OBJ 17)) E258) by (pose proof (pa_val_range (A_OBJ 17)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold cs_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) E257) by (pose proof (pa_val_range (A_OBJ 16)); lia).
rewrite (VB (A_OBJ 17) (VAL (A_OBJ 17)) E258) by (pose proof (pa_val_range (A_OBJ 17)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 FFS Hstk0 Hob0 Hob1 Hob16 Hob17 Hsep. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ + 8 <= _ \/ _ |- _ => clear H | H : _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok cs_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 FFS Hstk0 Hal32. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_grant_build_sweep's contract, adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v (the entry state and its region_ok facts), lib/A/AChf.v (the side-stack frame: aj_stack_malloc_atS, the realigned sp, reseat, the frame and shadow regions, the shadow_decl_ok alias), lib/A/ACb8.v (the chain pushed at a call, the flag store and the return) and lib/A/ACh1.v (a callee in afn_pre form through cl_callS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of the walk part of lib/A/Prog/GrantBuildSweepWalk.v at a working branch eacc832ec38a (blob 34c52c812f2, the blob the walk was ported from); A's GrantBuildSweep.v is the contract file, whose B form is GrantBContracts.v: the walk of reac_grant_build_sweep (0x855fc, 285 instructions) over image B's listing and walk layer, from the entry through the frame, the four -1 exits and the width checks to the loop (bs_main, with the loop's head pb_bs_head and its induction pb_bs_loop). GrantBuildSweepWalk.v composes it with the cell (GrantBuildSweepCell.v) and the tail (GrantBuildSweepTail.v) into GrantBContracts.v's walk_reac_grant_build_sweep. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC4b YC81 YC88 YCbw YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantSyms GrantList GrantAddr GrantTop GrantPa GrantPaLib GrantFrame GrantRo YC1g YC1h YC1i YC45 YC85
ACj1 ACbf GrantACjr GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBuildSweepLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* lia (Micromega) case-splits on every disjunction among the hypotheses it reads, and the walk's context holds many
   (the placement facts `x + n <= y \/ z <= x` of the frames, the table and the image, the shadow cell's range).
   rs_hide_all hides every disjunction of the context behind Datatypes.id (`change`, a conversion: no new term and no
   new constant), which lia reads as an atom; rs_show_all shows them again, and each step that needs one calls it
   after its `clear -`. Measured on this file (an internal proof-speed
   note): bs_main's four steps that add al's and the row's regions went from 43-76 s each to 7-14 s. *)
Local Ltac rs_hide_all := repeat match goal with H : ?A \/ ?B |- _ => change (Datatypes.id (A \/ B)) in H end.
Local Ltac rs_show_all := repeat match goal with H : Datatypes.id ?T |- _ => change T in H end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM2 : astack_malloc_realizes SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
(* the two program functions it calls, each as GrantBContracts.v states it *)
Hypothesis TEFF : C.tb_reac_headamp_tx_effective_spec B.
Hypothesis TBGS : C.tb_reac_ctrl_build_grant_sweep_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
(* ---- the entry state ----------------------------------------------------- *)
(* On image B the shadow-base cell is object 35 (image A: 32) and the use-after-return flag's cell object 36
   (image A: 33); the GOT words are objects 1 and 0 on both. The ATOM 32 is the shadow base on both. *)
Lemma bs_entry : forall W ly S regs mem md ch al base w shv,
afn_pre SEGS B BSW_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (bs_extra al base w shv))) ss_bs0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_grant_build_sweep)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch al base w shv HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : BSW_STK = 4832) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TL) in Kguar.
rewrite (pal_uar_cell B TL) in Kguar, Kuar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (bs_extra al base w shv))).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E276 : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E277 : ew E (A_OBJ 36) = Z_to_bv 64 (VAL (A_OBJ 36))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 35 ltac:(lia)) as Hob35. pose proof (pa_obj_img 36 ltac:(lia)) as Hob36.
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hob0, Hob1, Hob35, Hob36.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep. rewrite (pal_uar_cell B TL) in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_bs0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold bs_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
[cbn [sv_denot]; rewrite E276, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E276) by (pose proof (pa_val_range (A_OBJ 35)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 36) 0) (VAL (A_OBJ 36)));
[cbn [sv_denot]; rewrite E277, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 36)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 36) (VAL (A_OBJ 36)) E277) by (pose proof (pa_val_range (A_OBJ 36)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 36)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold bs_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E276) by (pose proof (pa_val_range (A_OBJ 35)); lia).
rewrite (VB (A_OBJ 36) (VAL (A_OBJ 36)) E277) by (pose proof (pa_val_range (A_OBJ 36)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob35 Hob36 Hsep. clear. unfold A_OBJ. cbn [Nat.add]. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok bs_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
(* The exit path reads no GOT word and no runtime cell: drop those regions, so that the flag byte's region
   has to be disjoint only from the windows this call owns (the machine stack, its frame and its shadow). *)
Ltac bs_drop_img HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in
(List.filter (fun r => match YP09.r_base r with
| Some n => negb ((Nat.eqb n (A_OBJ 0)) || (Nat.eqb n (A_OBJ 1)) || (Nat.eqb n (A_OBJ 35)) || (Nat.eqb n (A_OBJ 36)))
| None => true end) (ss_mem ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end; norm_ss HS.
(* ---- the way out of a -1 path: the flag store, the epilogue and the return ---- *)
Ltac bs_ret_m1 HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 Hbsw :=
let R1 := fresh "R1" in let R10 := fresh "R10" in let mat' := fresh "mat'" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
intros mat'; unfold C.tb_reac_grant_build_sweep_post, apost_base;
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
split; [let Hfr := fresh "Hfr" in pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr & _); exact Hfr|];
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly S2); exact Eab|];
split; [rewrite ES2; apply set_fs_free|];
rewrite Hbsw; split; [rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | let Hf := fresh "Hf" in intros Hf; discriminate Hf].
(* The flag region's disjointness obligations, the flag-store run and the return read only the state, the journal,
   the frame and flag facts, the stack's bounds and the atoms' values. Each lia call pays for every other fact in
   the context (about a hundred calls per exit), and it case-splits on the placement facts `x + n <= y \/ z <= x`
   (the frames against the image, the table against the frame, the two frames apart), which cost minutes per exit
   (measured by a Theorem Labs lane on the tail's exit: 376 s -> seconds). Drop them, the hidden facts, the kept-memory facts
   and every fact about the head-amp table before the exit. *)
Ltac bs_exit_prune :=
repeat match goal with
| H : _ + _ <= _ \/ _ <= _ |- _ => clear H
| H : Datatypes.id _ |- _ => clear H
| H : forall a : Z, _ -> aview _ _ _ a = _ |- _ => clear H end;
try (let t := lazymatch goal with _ : In (?t, C.ATx.TX_SIZE) _ |- _ => t end in
     repeat match goal with H : context [t] |- _ => clear H end).
Ltac bs_exit_m1 HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 fpos Hfin2 HFpres F FL E528 EFA0 Hsp1 FFS Hbsw :=
let HFLpres' := fresh "HFLpres'" in let HFLown' := fresh "HFLown'" in let HFLrng' := fresh "HFLrng'" in
let HnoF := fresh "HnoF" in let EFL0 := fresh "EFL0" in
assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity;
destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJ2) Hfin2) as (HFLpres' & HFLown' & HFLrng'); fold FL in HFLpres', HFLown', HFLrng';
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly S2 a) by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (proj2 (HFpres a Ha)));
bs_drop_img HS; bs_exit_prune;
add_flag_region HS AG E528 HFLpres' HFLrng' HFLown' HnoF HnoF HnoF;
paj_run_flag_sh RUNF HS HJ2; [lia | bs_wrange AG fpos F EFA0 EFL0 Hsp1 FFS | flag0 E528 EFL0 | bs_ret_m1 HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 Hbsw].
(* The same, on a path that has already seated al's two bytes and al's shadow cell: the flag byte must also
   miss al's bytes, which are in al's own frame, not owned by the client. *)
Ltac bs_exit_m1c HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 fpos Hfin2 HFpres HnoC F FL E528 EFA0 Hsp1 FFS Hbsw :=
let HFLpres' := fresh "HFLpres'" in let HFLown' := fresh "HFLown'" in let HFLrng' := fresh "HFLrng'" in
let HnoF := fresh "HnoF" in let EFL0 := fresh "EFL0" in
assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity;
destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJ2) Hfin2) as (HFLpres' & HFLown' & HFLrng'); fold FL in HFLpres', HFLown', HFLrng';
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly S2 a) by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (proj2 (HFpres a Ha)));
bs_drop_img HS; bs_exit_prune;
add_flag_region HS AG E528 HFLpres' HFLrng' HFLown' HnoC HnoC HnoF;
paj_run_flag_sh RUNF HS HJ2; [lia | bs_wrange AG fpos F EFA0 EFL0 Hsp1 FFS | flag0 E528 EFL0 | bs_ret_m1 HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 Hbsw].
(* ---- the preamble of a cut lemma ----------------------------------------- *)
(* Unpack a cut's three facts (bs_ctx, bs_env, bs_mem) into the names the walk tactics use: the entry facts
   (HPRE ..), the atoms' values (EE, E32 .. E621, E10 .. E13), the journal HJ2, the stack above sp HUP, the
   read-only data HRODc, the values HVALS, the table HOBJ, the own frame F (flag FL) and its bounds, al's
   frame (cid, pos) and its bounds, and the image facts (image B's bounds as numerals). *)
Ltac bs_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec :=
let L := rnLAWS in
destruct HCTX as (HPRE & Hroom & Htop32 & HROD & H10 & H11 & H12 & H13 & Rs & Rmx & Htx & HTlen & H01 & HTL & HSB &
Hsn & Haln & Hw1 & Hb8 & Hbw & Hfin & Hcid0 & Hflo & Hfhi & Hal8 & Hfrs2 & Eab & (fS2 & ES2) & Hsp1 & Hsp1al);
destruct HENV as (HEI & EE & E32 & E33 & E34 & E35 & E36 & E60 & RF & E528 & E529 & E619 & E620 & E621);
destruct HMEM as (HJ2 & HUP & HRODc & HVALS & HOBJ);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
assert (FFS : BSW_STK = 4832) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
lazymatch type of H10 with getr _ _ = w64 ?v => assert (E10 : ew Ec 10 = Z_to_bv 64 v) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10) end;
lazymatch type of H11 with getr _ _ = w64 ?v => assert (E11 : ew Ec 11 = Z_to_bv 64 v) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11) end;
lazymatch type of H12 with getr _ _ = w64 ?v => assert (E12 : ew Ec 12 = Z_to_bv 64 v) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12) end;
lazymatch type of H13 with getr _ _ = w64 ?v => assert (E13 : ew Ec 13 = Z_to_bv 64 v) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13) end;
lazymatch type of H10 with getr ?rg _ = _ => assert (Usp : bv_unsigned (ew Ec 2) = spZ rg) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity) end;
assert (AG : forall n, (n < 33)%nat -> ew Ec n = ew Ec n) by (intros; reflexivity);
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by (intros; reflexivity);
img_factsF Ec; img_hull_factsF;
rewrite ?IMG_LO_B_val, ?IMG_TOP_B_val in *;
pose proof (proj1 HJ2) as HAR2;
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity);
destruct (al_frames _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres);
destruct (frames_bounds _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh);
let HFIMG := fresh "HFIMG" in
pose proof (frm_off_imgB B _ _ _ _ _ 2 fpos HAR2 Hfin2) as HFIMG; rewrite IMG_LO_B_val, IMG_TOP_B_val in HFIMG;
destruct (frames_bounds _ _ L ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
let HCIMG := fresh "HCIMG" in
pose proof (frm_off_imgB B ly S W mem md cid pos HAR Hfin) as HCIMG; rewrite IMG_LO_B_val, IMG_TOP_B_val in HCIMG;
destruct (frame_al64 _ _ ly S W mem md cid pos HAR Hfin) as (Hf64 & Hfb64 & Hfb64');
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin);
let fl1 := fresh "fl1" in let fl2 := fresh "fl2" in let Efl := fresh "Efl" in
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ L ly S2 _ _ _ (2, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC;
destruct (al_blocks _ _ L ly S W mem md _ _ HAR Htx) as (_ & Htx4096 & Htxceil & Htxia & _);
change (req_size ATx.TX_SIZE) with 460 in Htxceil, Htxia;
pose proof Htx as HtxS2; rewrite <- Eab in HtxS2;
pose proof (sep_block_frame _ _ L ly S2 W _ _ _ _ 2 fpos HAR2 HtxS2 Hfin2) as HtxF;
unfold zdisjoint in HtxF; cbn [fst snd] in HtxF; change (req_size ATx.TX_SIZE) with 460 in HtxF;
change (fs_frame_bytes 2) with 256 in *;
let F := fresh "F" in let FL := fresh "FL" in
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : F / 8 + 32 <= 17592184995840) by (rewrite <- (Z.div_add F 32 8) by lia; apply Z.div_le_upper_bound; lia);
lazymatch type of H12 with getr _ _ = w64 ?al =>
assert (Hal512 : 512 <= al / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia);
assert (Hal8d : al = 8 * (al / 8)) by (pose proof (Z.div_mod al 8 ltac:(lia)); lia) end.
(* awrFL's rule for the row region (base atom 619 = F + 32 + 3c, three bytes, inside the own frame F). *)
Ltac awr_row_rule AG fpos F EFA Hc Hw1 :=
lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 619%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?cl, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 619%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
right; right; right; exists cl, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; fsb_lits; rewrite ?EFA; fold F; clear - Ha Hc Hw1; lia
| ] end.
(* ---- the head segment: from the loop head (0x85820) through al's shadow check (z = false: the slow path at
   0x85880 compares al & 7 = 0, read from the slot s1 + 0, with the cell's 2..7 and goes back to 0x8582c; the
   report call 0x8588c is not reached) and the column's load (s9 = (base + c) & 255) to the cell-loop head
   (0x85840) ---- *)
Lemma pb_bs_head : bs_head_spec B.
Proof.
unfold bs_head_spec.
intros z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos c Ec ms3 md3 Q HCTX Hc HENV HS HMEM K.
bs_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec.
assert (HKV : forall a, F + 32 <= a < F + 32 + 3 * c -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
assert (HKT : forall a, tx <= a < tx + 460 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
assert (HIMG : forall a, 0x10000 <= a < 0x5fb000 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
rs_hide_all.
destruct z.
all: paj_run_to_sh RUNTOP HS HJ2 19972; [awrFL_with ltac:(idtac; awr_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |].
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hc Hw1 HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Hc Hw1 HF4096 HFceil HFhigh HFIMG HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_rngW HKT HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Htx4096 Htxceil Htxia HtxF Hc Hw1 HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 HFIMG Hc Hw1 HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
1: bs_rejoin HS AG (bs_row :: bs_RL0 true) (bs_FL true 117 39) bs_al bs_deads_I 600%nat.
2: bs_rejoin HS AG (bs_row :: bs_RL0 false) (bs_FL false 117 39) bs_al bs_deads_I 600%nat.
all: ACj1.rebaseE HS AG HEv; clear HEv.
1: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with (ss_I true 0) in HS | idtac "HEADSEAT-T" ssx; fail] end.
2: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with (ss_I false 0) in HS | idtac "HEADSEAT-F" ssx; fail] end.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) => eapply (K Ev msx) end; [ unfold bs_env;
split; [lazymatch goal with H : img_env _ _ _ |- img_env _ _ ?Ev => lazymatch type of HS with st_ok_pi _ _ Ev _ _ => exact H end end|];
split; [intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32)] |]);
first [assumption | (rewrite (AG 32%nat) by lia; exact E32)]
| exact HS
| split; [exact HJ2|]; split; [exact HUP|]; split; [exact (rod_img_kept B W W _ _ HIMG HRODc)|]; split;
[ refine (garr8_aview_kept SEGS _ _ _ _ _ _ _ HVALS); intros a Ha; apply HKV; rewrite length_map, length_firstn, length_sweep_vals in Ha; lia
| apply (obj_at_transport_range SEGS _ _ tx ATx.LAY_TX (ATx.tx_vals T) 460 HOBJ); [vm_compute; reflexivity|];
intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia ] ].
Qed.
(* ---- the loop over the width, by induction on the columns left ---------- *)
Lemma pb_bs_loop : bs_cell_spec B -> bs_tail_spec B -> bs_loop_spec B.
Proof.
intros CELL TAIL. unfold bs_loop_spec.
intros z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos n.
induction n as [n IH] using lt_wf_ind.
intros c Ec ms3 md3 HCTX Hn Hc HENV HS HMEM.
eapply (pb_bs_head z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos c Ec ms3 md3 _ HCTX Hc HENV HS HMEM).
intros Ec0 ms0 md0 HENV0 HS0 HMEM0.
eapply (CELL z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos c 0 Ec0 ms0 md0 _ HCTX Hc ltac:(lia) HENV0 HS0
ltac:(rewrite Z.add_0_r; exact HMEM0)).
2, 3: intros Hp; discriminate Hp.
intros _ Ec1 ms1 md1 HENV1 HS1 HMEM1.
eapply (CELL z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos c 1 Ec1 ms1 md1 _ HCTX Hc ltac:(lia) HENV1 HS1
ltac:(replace (3 * c + 1) with (3 * c + 0 + 1) by lia; exact HMEM1)).
2, 3: intros Hp; discriminate Hp.
intros _ Ec2 ms2 md2 HENV2 HS2 HMEM2.
eapply (CELL z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos c 2 Ec2 ms2 md2 _ HCTX Hc ltac:(lia) HENV2 HS2
ltac:(replace (3 * c + 2) with (3 * c + 1 + 1) by lia; exact HMEM2)).
- intros Hp; lia.
- intros _ Hc1 Ec' ms' md' HENV' HS' HMEM'.
exact (IH (Z.to_nat (w - (c + 1))) ltac:(lia) (c + 1) Ec' ms' md' HCTX eq_refl ltac:(lia) HENV' HS' HMEM').
- intros _ Hc1 Ec' ms' md' HENV' HS' HMEM'.
exact (TAIL z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos Ec' ms' md' HCTX HENV' HS' HMEM').
Qed.
(* The two cut lemmas proved in GrantBuildSweepCell.v and GrantBuildSweepTail.v, taken here by name so that
   this file's walk does not wait on theirs; GrantBuildSweepWalk.v passes the proved ones. *)
Hypothesis CELL : bs_cell_spec B.
Hypothesis TAIL : bs_tail_spec B.
(* ---- the walk ------------------------------------------------------------ *)
Lemma bs_main : C.tb_reac_grant_build_sweep_spec B.
Proof.
unfold C.tb_reac_grant_build_sweep_spec.
intros ly S W regs mem md ch s mx al tx base w T HPRE Hroom Htop32 HROD H10 H11 H12 H13 Rs Rmx Ral HAL Htx HTlen HTX H01 HTL HSB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
set (shv := match aview SEGS (w_H W) mem (SB + al / 8) with Some v => v | None => 0 end).
pose proof (bs_entry W ly S regs mem md ch al base w shv HPRE) as HS.
pose proof (ajournal_init SEGS B BSW_STK (C.tb_reac_grant_build_sweep_FP s al mx base w) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : BSW_STK = 4832) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs (bs_extra al base w shv))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 mx) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 al) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 tx) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (bs_extra al base w shv) (Z_to_bv 64 0))
by (intros j Hj; subst E; eimg_low; apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth bs_extra map] in E32, E33, E34, E35, E36. clear EX.
img_factsF E. img_hull_factsF.
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hob241, Hob242, Hob276, Hob277, Huar.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (bs_extra al base w shv)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_grant_build_sweep)) with (Z_to_bv 64 (BASE + AF_reac_grant_build_sweep)).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
(* the head-amp table's bytes and image B's own bytes stay as they are *)
destruct (al_blocks _ _ LAWS ly S W mem md tx ATx.TX_SIZE HAR Htx) as (_ & Htx4096 & Htxceil & Htxia & _).
change (req_size ATx.TX_SIZE) with 460 in Htxceil, Htxia.
pose proof (blk_off_imgB B ly S W mem md tx ATx.TX_SIZE HAR Htx) as HtxIMG.
change (req_size ATx.TX_SIZE) with 460 in HtxIMG. rewrite IMG_LO_B_val, IMG_TOP_B_val in HtxIMG.
assert (HKTX : forall a, tx <= a < tx + 460 -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by (intros; reflexivity).
assert (HIMG : forall a, 0x10000 <= a < 0x5fb000 -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by (intros; reflexivity).
(* ---- to the instruction after `andi sp,sp,-32` (0x85640) ---- *)
paj_run_to_sh RUNTOP HS HJ 19460. { awrFL AG 0 0 EFA0. }
upd_rngW HKTX HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp Htx4096 Htxceil Hceil Hslo Hstk0 Hshi H47 FFS C1; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp Hceil Hslo Hstk0 Hshi H47 FFS C1; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_aboveW_init HFr AG HUP. clear_frames. cbn [ms_mem mkst] in HUP.
(* ---- the realigned sp (atom 60) and the frame's slots ---- *)
set (sp1 := 32 * ((spZ regs + -192) / 32)).
destruct (sp1_facts (spZ regs + -192) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-192) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(clear - Hshi H47; lia) ltac:(clear - Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. ACj1.rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2;
rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
change (2 ^ 5) with 32; clear - Hsp1 Hsp1al Hslo Hstk0 Hshi H47 Hceil FFS C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 88 0 88 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; clear - Ho Hsp1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 Hob241 Hob242 Hob276 Hob277 Huar; repeat split; zone_lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* ---- to the call of __asan_stack_malloc_2 (0x85674) ---- *)
paj_run_shc RUNP RUNC HS HJ. { awrFL AG 0 0 EFA0. }
upd_rngW HKTX HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 Htx4096 Htxceil Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_aboveW HUP HFr AG. clear HF HFr HG.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm2 B TLF).
pose proof (count_cid_le_length 2 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 2 ASM2 ltac:(lia) W (ms_regs msX) (ms_mem msX) BSW_STK (spZ regs) (C.tb_reac_grant_build_sweep_FP s al mx base w) ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
- unfold spZ at 1. rewrite R2. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- clear - Hsp1; lia.
- rewrite FFS, Hes; clear - Hsp1; lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- change (fs_frames 2) with 4096. clear - Hcnt Hroom; lia. }
cbv beta. clear R2 R3 R4 R1 HJ.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
(* the table's bytes and the read-only data across the call *)
assert (HKTX2 : forall a, tx <= a < tx + 460 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HKTX a Ha). pose proof HJin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & JB & _).
replace a with (tx + (a - tx)) by lia. apply (JB tx ATx.TX_SIZE (a - tx) Htx); [rewrite Eab; exact Htx | change (req_size ATx.TX_SIZE) with 460; lia | apply inFP_nil]. }
pose proof (rod_img_kept B W W _ _ HIMG HROD) as HROD1.
rewrite Hes in HK. replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by (clear; lia).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
pose proof (rod_acall_kept B ly S W W _ mem2 _ _ _ HK HROD1) as HRODc.
clear HKTX HIMG HROD1 HJin. rename HKTX2 into HKTX.
assert (HIMG : forall a, 0x10000 <= a < 0x5fb000 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a) by (intros; reflexivity).
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; clear - Ha Hsp1 Hceil Hslo Hstk0 FFS C1; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly S2 W _ _ tx ATx.TX_SIZE 2 fpos HAR2 ltac:(rewrite Eab; exact Htx) Hfin2) as HtxF.
unfold zdisjoint in HtxF. cbn [fst snd] in HtxF. change (req_size ATx.TX_SIZE) with 460 in HtxF.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgB B ly S2 W mem2 md2 2 fpos HAR2 Hfin2) as HFIMG.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HFIMG. change (fs_frame_bytes 2) with 256 in HFIMG.
change (fs_frame_bytes 2) with 256 in *.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. ACj1.rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (HF8c : F / 8 + 32 <= 17592184995840) by (rewrite <- (Z.div_add F 32 8) by lia; apply Z.div_le_upper_bound; lia).
rs_hide_all.
destruct (FFL ly S2 W mem2 md2 2 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 152 256 152 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 248 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 248) with (F + 256 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 32 152 32 152 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (ZS : forall j, 0 <= j < 4 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (256 / 8) with 32. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 2 0 32 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2 / 8) with 32; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (256 / 8) with 32; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 16 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 16) with (SB + F / 8 + 8 * 2) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 24 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 24) with (SB + F / 8 + 8 * 3) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2 / 8) with 32; rewrite E529, RF; evalE AG; ulits; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* ---- to `beqz s3` (0x85748): s = 0 ---- *)
paj_run_sh RUNP HS HJ2. { awrFL AG fpos F EFA0. }
upd_rngW HKTX HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_aboveW HUP HFr AG. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* s = 0: -1, out through the flag store *)
assert (Hs0 : s = 0).
{ rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
lazymatch type of Hc with U ?Ev _ = _ => rewrite (U_atom Ev 10 s) in Hc; [| rewrite (AG 10%nat) by lia; exact E10 | lia] end.
change (U _ (SLit 0)) with 0 in Hc. exact Hc. }
assert (Hbsw : bsw_ok s al mx base w = false) by (unfold bsw_ok; rewrite Hs0; reflexivity).
bs_exit_m1 HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 fpos Hfin2 HFpres F FL E528 EFA0 Hsp1 FFS Hbsw.
- assert (Hsn : s <> 0).
{ rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
lazymatch type of Hc with U ?Ev _ <> _ => rewrite (U_atom Ev 10 s) in Hc; [| rewrite (AG 10%nat) by lia; exact E10 | lia] end.
change (U _ (SLit 0)) with 0 in Hc. exact Hc. } clear Hc.
(* ---- to `beqz s6` (0x8574c): al = 0 ---- *)
paj_run_sh RUNP HS HJ2. { awrFL AG fpos F EFA0. }
upd_rngW HKTX HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
upd_aboveW HUP HFr AG. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
+ assert (Hal0 : al = 0).
{ rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
lazymatch type of Hc with U ?Ev _ = _ => rewrite (U_atom Ev 12 al) in Hc; [| rewrite (AG 12%nat) by lia; exact E12 | lia] end.
change (U _ (SLit 0)) with 0 in Hc. exact Hc. }
assert (Hbsw : bsw_ok s al mx base w = false) by (unfold bsw_ok; rewrite Hal0, Z.eqb_refl; cbn [negb]; rewrite andb_false_r; reflexivity).
bs_exit_m1 HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 fpos Hfin2 HFpres F FL E528 EFA0 Hsp1 FFS Hbsw.
+ assert (Haln : al <> 0).
{ rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
lazymatch type of Hc with U ?Ev _ <> _ => rewrite (U_atom Ev 12 al) in Hc; [| rewrite (AG 12%nat) by lia; exact E12 | lia] end.
change (U _ (SLit 0)) with 0 in Hc. exact Hc. } clear Hc.
destruct (HAL Haln) as (HFO & HG8).
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hal8 & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgB B ly S W mem md cid pos HAR Hfin) as HCIMG.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HCIMG.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hfin) as (Hf64 & Hfb64 & Hfb64').
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos SEGS B LAWS ly S2 W mem2 md2 (2, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 2) with 256 in HdFC. fold F in HdFC.
assert (Hb8 : 0 <= base < 256) by (destruct (HG8 0%nat ltac:(cbn; lia)) as [_ X]; exact X).
assert (Hw8 : 0 <= w < 256) by (destruct (HG8 1%nat ltac:(cbn; lia)) as [_ X]; exact X).
destruct (HRA (al + 1) ltac:(lia)) as (sv0 & Hsv0 & Hsok).
assert (Hdiv1 : (al + 1) / 8 = al / 8).
{ rewrite (Z.div_mod al 8) at 1 by lia. rewrite Hal8, Z.add_0_r.
replace (8 * (al / 8) + 1) with (1 + (al / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
assert (Hal8d : al = 8 * (al / 8)) by (pose proof (Z.div_mod al 8 ltac:(lia)); lia).
assert (Esh : shadow_of_addr SHADOW_OFF (al + 1) = SB + al / 8) by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF, Hdiv1; reflexivity).
rewrite Esh in Hsv0.
assert (Eshv : shv = sv0) by (unfold shv; rewrite Hsv0; reflexivity).
assert (Hsv0r : sv0 = 0 \/ 2 <= sv0 <= 7).
{ destruct Hsok as [H0 | [H1 H2]]; [left; exact H0 | right].
replace ((al + 1) mod 8) with 1 in H1; [lia|]. rewrite Zplus_mod, Hal8. reflexivity. }
assert (HnoC : forall a, al <= a < al + 2 -> ~ aowned B ly S2 a).
{ intros a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 HfinS2) as (_ & _ & HCp & _). apply (proj2 (HCp a ltac:(lia))). }
rs_hide_all.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JF4 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msX) =>
assert (HALc : forall j, (j < 2)%nat -> val_mem SEGS (mrestrict (w_H W) (ms_mem msX)) (al + Z.of_nat j) 1 (nth j [base; w] 0));
[ intros j Hj; apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem (ms_mem msX)); [| apply HG8; exact Hj];
intros x Hx; cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hx;
apply (JF4 cid pos x Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; destruct j as [|[|]]; cbn in Hx; lia
| apply (bsw_fp_frames B LAWS ly S W mem md s al mx base w HAR HSB cid pos x Hfin); left; unfold in_zr, frame_rng; cbn [fst snd]; destruct j as [|[|]]; cbn in Hx; lia]
| ];
assert (HSHc : aview SEGS (w_H W) (ms_mem msX) (SB + al / 8) = Some sv0);
[ rewrite <- Hsv0;
assert (Hshin : in_zr (SB + al / 8) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8));
[ unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
pose proof (shadow_in_frame (frame_addr ly cid pos) (fs_frame_bytes cid) al Hf64 Hfb64 ltac:(lia) ltac:(lia) ltac:(lia)); lia | ];
apply (JF4 cid pos _ Hfin (or_intror Hshin)); apply (bsw_fp_frames B LAWS ly S W mem md s al mx base w HAR HSB cid pos _ Hfin (or_intror Hshin))
| ] end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E12' : ew Ev 12 = Z_to_bv 64 al) by (rewrite (AG 12%nat) by lia; exact E12) end.
assert (Hal512 : 512 <= al / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
(* al's two bytes, its shadow cell and the two alias facts the shadow checks need *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 12 (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E12', unsigned_lit_small by lia; change (2 ^ 3) with 8; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 33 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 34 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 35 (mkAF (SB + 512) (SB + 17592186044416) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by (unfold SB; lia); rewrite Z.pow_0_r, Z.mod_1_r; unfold SB; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 12 32 35 al SB E12' ltac:(lia) E32' E35)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_okc Ev 12 32 35 al SB 1 E12' ltac:(lia) ltac:(lia) ltac:(lia) Hdiv1 E32' E35)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 12%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E12', unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ al 0 1 _ base); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (HALc 0%nat ltac:(lia))]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ al 1 1 _ w); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (HALc 1%nat ltac:(lia))]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E12', RF; evalE AG; ulits;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG HF8lo HF8hi HF8c Hf4096 Hfceil Hfhigh HCIMG HdFC Hflo Hfhi Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
unfold Datatypes.id in Hsv0r.
destruct Hsv0r as [Hz0 | Hz2].
1: ( (* al's shadow cell holds 0 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msX) =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E35, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + al / 8) 0 1 _ 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; rewrite Hz0 in HSHc; exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ HSHc))]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E35, E12', E529, RF; evalE AG; ulits; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG HF8lo HF8hi HF8c Hf4096 Hfceil Hfhigh HCIMG HdFC Hflo Hfhi Hal512 Hal8d HF8 HFq Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS).
2: ( (* al's shadow cell holds 2..7 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msX) =>
pose proof (st_ok_pi_add_fact Ev _ _ 36 (mkAF 2 7 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E36, Eshv, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E35, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + al / 8) 0 1 _ sv0); [cbn [sv_denot]; rewrite E36, Eshv, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ HSHc))]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E35, E12', E529, RF; evalE AG; ulits; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG HF8lo HF8hi HF8c Hf4096 Hfceil Hfhigh HCIMG HdFC Hflo Hfhi Hal512 Hal8d HF8 HFq Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS).
(* ---- to `bltu` at 0x85774: 1 <= width <= 40 ---- *)
all: paj_run_sh RUNP HS HJ2; [awrFL AG fpos F EFA0 |].
all: upd_rngW HKTX HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: psrr_branch_pi RUNP BR HS.
1,3: (assert (Hbsw : bsw_ok s al mx base w = false);
[ rewrite branch_ltu_U, U_SOff, U_SLit, E34, unsigned_lit_small in Hc by lia; unfold zcanon, M64 in Hc;
rewrite (Z.mod_small 18446744073709551576) in Hc by lia; apply Z.ltb_lt in Hc; exact (bsw_bad_w s al mx base w Hw8 Hc)
| bs_exit_m1c HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 fpos Hfin2 HFpres HnoC F FL E528 EFA0 Hsp1 FFS Hbsw ]).
all: assert (Hw1 : 1 <= w <= 40) by (rewrite branch_ltu_U, U_SOff, U_SLit, E34, unsigned_lit_small in Hc by lia; unfold zcanon, M64 in Hc;
rewrite (Z.mod_small 18446744073709551576) in Hc by lia; apply Z.ltb_ge in Hc; exact (bsw_good_w w Hw8 ltac:(lia))); clear Hc.
(* ---- to `bltu` at 0x857a0: base + width <= 48 ---- *)
all: paj_run_sh RUNP HS HJ2; [awrFL AG fpos F EFA0 |].
all: upd_rngW HKTX HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: psrr_branch_pi RUNP BR HS.
all: lazymatch goal with
| Hc : branch_taken _ _ _ = true |- _ =>
(assert (Hbsw : bsw_ok s al mx base w = false);
[ rewrite branch_ltu_U, (bsw_fits_U _ base w E33 E34 ltac:(lia) ltac:(lia)), U_SLit in Hc;
unfold zcanon, M64 in Hc; rewrite (Z.mod_small 18446744073709551568) in Hc by lia;
apply Z.ltb_lt in Hc; exact (bsw_bw_bad s al mx base w Hb8 ltac:(lia) Hc)
| bs_exit_m1c HS HJ2 AG EE Hra Hsegs Eab ly S2 ES2 fpos Hfin2 HFpres HnoC F FL E528 EFA0 Hsp1 FFS Hbsw ])
| Hc : branch_taken _ _ _ = false |- _ =>
(assert (Hbw : base + w <= 48) by
(rewrite branch_ltu_U, (bsw_fits_U _ base w E33 E34 ltac:(lia) ltac:(lia)), U_SLit in Hc;
unfold zcanon, M64 in Hc; rewrite (Z.mod_small 18446744073709551568) in Hc by lia;
apply Z.ltb_ge in Hc; exact (bsw_bw_good base w Hb8 Hw8 Hc)); clear Hc)
end.
(* ---- the unpoisoning of the values buffer, the redundant width check at 0x857e4 and the slots; to the loop
   head (0x85820). The engine decides 0x857e4 itself: its condition `w - 41 >=u -40` is the negation of the
   branch at 0x85774, which the run recorded as a fact when it went on. ---- *)
all: paj_run_to_sh RUNTOP HS HJ2 19940; [awrFL AG fpos F EFA0 |].
all: upd_rngW HKTX HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; rs_show_all; revert Hrg_rng; evalE AG; intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
(* ---- seat the loop head on ss_L (c = 0): the row atom 619 = F + 32, the row index 620 = 0 and the
   column 621 = 0, the three row aliases, and the row's three bytes as a region ---- *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 619 Ev ssv msv [Z_to_bv 64 (F + 32); Z_to_bv 64 0; Z_to_bv 64 0] HS ltac:(vm_compute; reflexivity)) as HS3 end.
all: clear HS; rename HS3 into HS; ACj1.rebaseE HS AG HEv.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E619 : ew Ev 619 = Z_to_bv 64 (F + 32))
by (rewrite HEv; exact (ew_havoc_new _ 619 [Z_to_bv 64 (F + 32); Z_to_bv 64 0; Z_to_bv 64 0] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E620 : ew Ev 620 = Z_to_bv 64 0)
by (rewrite HEv; exact (ew_havoc_new _ 619 [Z_to_bv 64 (F + 32); Z_to_bv 64 0; Z_to_bv 64 0] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E621 : ew Ev 621 = Z_to_bv 64 0)
by (rewrite HEv; exact (ew_havoc_new _ 619 [Z_to_bv 64 (F + 32); Z_to_bv 64 0; Z_to_bv 64 0] 2 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
all: clear HEv.
all: prreg HS (18%bv : bv 5) R18c; prreg HS (27%bv : bv 5) R27c.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (18%bv : bv 5) (SOff 621 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E621, Z.add_0_r, R18c; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
all: norm_ss HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (27%bv : bv 5) (SOff 620 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E620, Z.add_0_r, R27c; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
all: norm_ss HS. all: clear R18c R27c.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 619 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E619, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 620 (mkAF 0 117 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E620, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 621 (mkAF 0 39 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E621, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (bs_alias_ok Ev F 0 0 RF ltac:(rewrite E619; f_equal; lia) ltac:(rewrite E620; f_equal; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (bs_alias_ok Ev F 0 1 RF ltac:(rewrite E619; f_equal; lia) ltac:(rewrite E620; f_equal; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (bs_alias_ok Ev F 0 2 RF ltac:(rewrite E619; f_equal; lia) ltac:(rewrite E620; f_equal; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the values buffer's region (516, 32..152) gives way to the row's three bytes; the row's presence comes from
   the frame law over the current memory (HFpres above is over the memory right after the allocation) *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in
(List.filter (fun r => negb (match YP09.r_base r with Some n => Nat.eqb n 516 | None => false end && Z.eqb (YP09.r_lo r) 32)) (ss_mem ssx)) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
all: norm_ss HS.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpresN & _).
all: change (fs_frame_bytes 2) with 256 in HFpresN.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ bs_row HS eq_refl
ltac:(unfold region_ok, bs_row; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E619, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); replace (F + 32 + o) with (F + (32 + o)) by lia; apply (proj1 (HFpresN (F + (32 + o)) ltac:(lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, bs_row; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?E619, ?E35, ?E12', ?E529, ?RF, ?E60; evalE AG; ulits; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFIMG HF8lo HF8hi HF8c Hf4096 Hfceil Hfhigh HCIMG HdFC Hflo Hfhi Hal512 Hal8d HF8 HFq Hob241 Hob242 Hob276 Hob277 Huar; rs_show_all;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
all: norm_ss HS.
1: bs_rejoin HS AG (bs_row :: bs_RL0 true) (bs_FL true 117 39) bs_al bs_deads 600%nat.
2: bs_rejoin HS AG (bs_row :: bs_RL0 false) (bs_FL false 117 39) bs_al bs_deads 600%nat.
all: ACj1.rebaseE HS AG HEv; clear HEv.
1: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with (ss_L true) in HS | idtac "SEATFAIL-T" ssx; fail] end.
2: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with (ss_L false) in HS | idtac "SEATFAIL-F" ssx; fail] end.
all: rs_show_all.
all: assert (HCTX : bs_ctx B ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos)
by (unfold bs_ctx; repeat (split; [first [assumption | exact (ex_intro _ fS2 ES2) | lia] |]); first [assumption | lia]).
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (HENV : bs_env regs al base w shv sp1 F FL 0 Ev);
[ unfold bs_env;
split; [lazymatch goal with H : img_env _ _ Ev |- _ => exact H end|];
split; [intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32) | (rewrite E619; f_equal; lia) | (rewrite E620; f_equal; lia)] |]);
first [assumption | (rewrite E621; f_equal; lia)] | ] end.
all: first [ refine (pb_bs_loop CELL TAIL true ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos (Z.to_nat (w - 0)) 0 _ _ _ HCTX eq_refl ltac:(lia) HENV HS _)
| refine (pb_bs_loop CELL TAIL false ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos (Z.to_nat (w - 0)) 0 _ _ _ HCTX eq_refl ltac:(lia) HENV HS _) ].
all: split; [exact HJ2|]; split; [exact HUP|]; split; [exact (rod_img_kept B W W _ _ HIMG HRODc)|]; split; [cbn; apply garr8_nil|].
all: apply (obj_at_transport_range SEGS _ _ tx ATx.LAY_TX (ATx.tx_vals T) 460 HTX); [vm_compute; reflexivity|].
all: intros i Hi; apply (mbyte_of_aview SEGS); apply HKTX; lia.
Qed.
End e.
End d.
End b.

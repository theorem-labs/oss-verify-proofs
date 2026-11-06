(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module paths and module names changed; 422 of its 488 lines of code are new or changed and 222 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_ignored.v, with its module paths and module names changed; 78 of its 130 lines of code are new or changed and 436 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan, 0x8a218 = BASE +
   AF_reac_declared_vlan_split): the image-B port of lib/A/Prog/reac_declared_vlan_split_k.v
   (commit ceb7e39832b2). Image B's listing object 0 is the GOT word 0xa3210 and object 12 the
   shadow-base cell 0xac7b8 (lib/B/Prog/SegAddr.v seg_objs), the same positions as image A's.
   The kit of its walk: the symbolic entry state and its seed (the 64-byte frame below sp, the GOT word of the
   shadow-base cell, listing object 0, and the cell itself, object 12, whose word is the shadow base atom 32); the
   stack the walk asks; the first run, from the entry over the four `beqz` tests (the atom facts of a0, a1, a3 and
   a2 = 16 decide them) and the two loads of the shadow base to the call of the strrchr wrapper at 0x8a274. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the stack the walk asks below the entry sp, image B's instance file's SegInstB.STK_reac_declared_vlan_split
   (12,352), under the name the segments use: its 64-byte frame and below it the widest window it calls, the strtol
   wrapper's 3 * ESTACK (RtSeg.astrtol0_realizes); the strrchr wrapper asks 2 * ESTACK, the strlen wrapper and the
   checked memcpy ESTACK, name_ok SegInstB.STK_name_ok = 64 + ESTACK (its frame and isalnum's window) *)
Notation VS_STK := SegInstB.STK_reac_declared_vlan_split (only parsing).
Notation NAME_OK_STK := SegInstB.STK_name_ok (only parsing).

(* atoms of the entry state: 0-31 the registers, 32 the shadow base SB (the word of the cell, listing object 12) *)
Definition vs_regions0 : smem := [stack_region 64; got_regionP; bcell_regionP 32].
Definition vs_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (10%nat, mkAF 4096 (2 ^ 47 - 1) 0);
    (11%nat, mkAF 4096 (2 ^ 47 - 1) 0); (12%nat, mkAF 16 16 0); (13%nat, mkAF 4096 (2 ^ 47 - 1) 1)] [] [].
Definition vs_ss0 : sstate := mkSS AF_reac_declared_vlan_split sr_atoms vs_regions0 None vs_facts0.
Definition vs_extra0 : list word := [Z_to_bv 64 SB].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* the listing's objects 0 and 12 are the record's GOT word of the shadow-base cell and the cell (PALib) *)
Hypothesis TL : PALib B.

Lemma vs_EE : forall (regs : bvmap 5 word) extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof using.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma vs_E32 : forall (regs : bvmap 5 word) v, ew (Eimg (Ereg regs [Z_to_bv 64 v])) 32 = Z_to_bv 64 v.
Proof using. intros regs v. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma vs_Eobj : forall E i, (i < 13)%nat -> img_env VAL A_LIM E -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof using.
intros E i Hi HE. pose proof (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as H.
apply bv_eq. rewrite H. rewrite unsigned_lit_small; [reflexivity|]. exact (pa_val_range (A_OBJ i)).
Qed.

(* the symbolic entry state holds of the entry configuration *)
Lemma vs_seed : forall W regs mem ly S md ch seg parent vid,
  afn_pre SEGS B VS_STK ly S W regs mem md ch ->
  getr regs 10 = w64 seg -> 4096 <= seg <= 2 ^ 47 - 1 ->
  getr regs 11 = w64 parent -> 4096 <= parent <= 2 ^ 47 - 1 ->
  getr regs 12 = w64 16 ->
  getr regs 13 = w64 vid -> 4096 <= vid <= 2 ^ 47 - 1 -> vid mod 2 = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs vs_extra0)) vs_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_declared_vlan_split)) mem (seg_rom SEGS))).
Proof using LAWS TL.
intros W regs mem ly S md ch seg parent vid HPRE H10 R10 H11 R11 H12 H13 R13 A13.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HVS : VS_STK = 12352) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
set (E := Eimg (Ereg regs vs_extra0)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (vs_EE regs _ 2 2%bv eq_refl); reflexivity).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply vs_E32).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply vs_Eobj; [lia | exact HEI]).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply vs_Eobj; [lia | exact HEI]).
pose proof (pa_obj_img 0 ltac:(lia)) as O0. pose proof (pa_obj_img 12 ltac:(lia)) as O12.
pose proof (pal_got_cell B TL) as Ogc.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold vs_ss0. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold vs_regions0, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (unfold kImgEnd in *; lia).
    split; [lia|]. split; [unfold kImgEnd in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold kImgEnd in *; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by (unfold kImgEnd in *; lia).
    split; [lia|]. split; [unfold kImgEnd in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold vs_regions0, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by (unfold kImgEnd in *; lia).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 Hstk0 O0 O12 Ogc. unfold kImgEnd. clear. intros. repeat split; lia.
- split; [|split; exact I]. cbn [vs_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E32, (EV 10%nat 10%bv eq_refl), (EV 11%nat 11%bv eq_refl), (EV 12%nat 12%bv eq_refl),
    (EV 13%nat 13%bv eq_refl), H10, H11, H12, H13.
  unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 1) with 2. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0 R10 R11 R13 A13. unfold SB. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the first run: from the entry to the strrchr wrapper's call *)
Definition vs_ss1 : sstate := Eval vm_compute in fst (sym_runN_pi seg_tpi FUEL vs_ss0).
Lemma vs_run1 : sym_runN_pi seg_tpi FUEL vs_ss0 = (vs_ss1, PRS_call SS___interceptor_trampoline_strrchr).
Proof using. vm_compute. reflexivity. Qed.
End e.
End f.
End d.

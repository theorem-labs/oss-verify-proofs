(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 94 of its 139 lines of code are new or changed and 359 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the pieces that the two arms (op_write +0x8e4, op_decide +0x648)
   share. Each arm runs the image's instructions symbolically (LinkWalk.v paj_run_x over the walk's journal) between
   its calls, and applies its callees' contracts at each call under SRr_bind.
   - aw_ms_eq: a machine state at a cut (lf_shape) is the mkst at the running FP state.
   - aw_entry0: the symbolic state of a register-only stretch (no memory region), at any pc of the listing; the
     atom 2 (sp) is placed in [2 ^ 46, 2 ^ 47] and 16-aligned, the atom 32 is the shadow base (the token runner's
     Bx), as every walk of link states them (model_decide.v d_facts).
   - aw_entry1: the same with one 8-byte region at sp + off holding the atom 33 (a spill slot the stretch loads).
   - aw_stk_shadow: a byte range of the real-stack row is addressable and its shadow hull visible at every AR state
     (AR's zero-shadow law for the row, the layout's page alignment: lib/A/AE3h.v vf_stack_shadow, generic).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition AW_SB : Z := 0x7fff8000.
Definition aw_Bx : sv := SOff 32 0.
Definition aw_span : Z * Z := (AW_SB, AW_SB + 2 ^ 44 - 1).

(* a register-only stretch *)
Definition aw_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF AW_SB AW_SB 0)] [] [].
Definition aw_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None aw_facts0.
Definition aw_extra0 : list word := [Z_to_bv 64 AW_SB].

(* a stretch that loads one 8-byte spill slot at sp + off *)
Definition aw_slot (off : Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 33 0))].
Definition aw_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF AW_SB AW_SB 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition aw_ss1 (pc off : Z) : sstate := mkSS pc sr_atoms [aw_slot off] None aw_facts1.
Definition aw_extra1 (v : Z) : list word := [Z_to_bv 64 AW_SB; Z_to_bv 64 v].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* a machine state at a cut is the mkst of its registers and memory at the running FP state *)
Lemma aw_ms_eq : forall (fy : YK11.FPState) pc ms, lf_shape fy pc ms ->
  ms = @YK11.mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros fy pc [regs fregs pcv svc resv fcsr mem rom] (H1 & H2 & H3 & H4 & H5 & H6).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *. subst.
  reflexivity.
Qed.

(* the entry state of a register-only stretch *)
Lemma aw_entry0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs aw_extra0)) (aw_ss0 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem pc Hsp H16.
  set (E := Eimg (Ereg regs aw_extra0)).
  assert (E2 : ew E 2 = getr regs 2)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 AW_SB)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  rewrite restrict_mkst_fx. unfold aw_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [|split; [exact I | exact I]].
    cbn [aw_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, !unsigned_lit_small by (unfold AW_SB; lia).
    change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold AW_SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the entry state of a stretch that loads the slot [sp + off, sp + off + 8), which holds v *)
Lemma aw_entry1 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc off v,
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= off < 2 ^ 20 -> 0 <= v < 2 ^ 64 ->
  regions_wf [aw_slot off] = true ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + off) 8 v ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (aw_extra1 v))) (aw_ss1 pc off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem pc off v Hsp H16 Hoff Hv Hwf Hval.
  set (E := Eimg (Ereg regs (aw_extra1 v))).
  assert (E2 : ew E 2 = getr regs 2)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 AW_SB)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 v)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  rewrite restrict_mkst_fx. unfold aw_ss1. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - exact Hwf.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, aw_slot.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (spZ regs) off 8 (SOff 33 0) v);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia |].
    exact Hval.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [aw_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, E33, !unsigned_lit_small by (unfold AW_SB; lia).
    change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold AW_SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the real-stack row's bytes are addressable and their shadow hull visible, at every AR state *)
Lemma aw_stk_shadow : forall (W : world SEGS) ly S mem md a n,
  AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) a n).
Proof.
  intros W ly S mem md a n HAR Hlo Hhi Hn.
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity))
    as Hz.
  cbn [fst snd] in Hz. unfold zero_shadow in Hz.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  split.
  - intros y Hy. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
      by (unfold shadow_of_addr; lia).
    apply Hz. clear - Hy Lplo Lphi Hlo Hhi Hn. lia.
  - intros Hn0 s Hs.
    replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
    rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
    clear - Hs Hn0 Lplo Lphi Hlo Hhi Hn. unfold SHADOW_OFF in *. lia.
Qed.

End b.
End a.

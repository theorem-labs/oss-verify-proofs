(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the leaves of segment S0 of the ASan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput, split out of lib/A/P_LLVMFuzzerTestOneInput_S0.v (a working branch
   67f0c71b18d) so that its twelve input-length cases compile in parallel (P_LLVMFuzzerTestOneInput_S0_n*.v).
   Everything up to `s0_c1` is that file's text, unchanged, except that its Ltacs are defined after the
   Sections (a Section forgets its Ltacs).  Added: `s0_case_stmt`, seg_S0_stmt on the input lengths n with
   C n; `s0_cases`, seg_S0_stmt from the twelve cases; `rs_hold`, a hypothesis lia does not see.
   The one-file header follows. *)
(* Modified by Theorem Labs, 2026-10: segment S0 of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput
   (fuzz_scene.asan): the entry 0x82878 .. the cut C1 0x82b78 of lib/A/P_LLVMFuzzerTestOneInput_seg.v.  The
   statement `seg_S0_stmt` is a Theorem Labs lane's, PASSED and unchanged; this file only proves it (`scene_seg_S0`). *)

(*   The walk, on the position-abstract kit (lib/A/Prog/{PaRun,PaShadow,ScenePaLib,SceneFrame,SceneACj*}):
   - `s0_entry`: the entry state from afn_pre (the GOT words of the shadow base and of the use-after-return flag,
     and the flag cell, whose value 1 is al_const's -- ENTRY-REVIEW.md R4: the flag is read, never assumed);
   - the prologue and the 13-word save area 0x82878-0x828b8; sp1 = (sp - 224) & -32 becomes atom 60;
   - the GOT reads, the flag test 0x828e0 (decided: flag = 1) and __asan_stack_malloc_8(9408) at 0x828ec through
     a Theorem Labs lane's `aj_stack_malloc_sz_at` (lib/A/J_StackSzPf.v) at class 8; the real-stack arm 0x82904-0x82924 is
     dead because `bnez s7` 0x82900 is decided by the fake frame's range (F >= 4096);
   - a Theorem Labs lane's `frame_setup SEGS VAL B 8 9408` (lib/A/P_check_step_frame.v) for the frame and frame-shadow regions;
   - the frame header and the 28 inline shadow stores 0x82928-0x829dc, __asan_set_shadow_f8(shF + 0x1c, 1113) at
     0x829e0 through `aj_set_shadow_at` (lib/A/J_StackSzPf.v), the 35 stores 0x829ec-0x82a74;
   - the early return `bnez a1` 0x82a78 (a1 = n >> 26) refuted from n < 2 ^ 26;
   - the input parse 0x82a7c-0x82b28 / 0x830c4-0x83140, the mac unpoison 0x82b1c and the 6-turn mac loop
     0x82b2c-0x82b60, in twelve cases n = 0 .. 10 (s5 pinned to the literal) and n >= 11;
   - `s0_c1`: the cut C1 assembled once from what each case establishes at 0x82b78.
   ASan report branches: every shadow check of the walk (0x82a90, 0x82ac4, 0x830d0, 0x83104, 0x83130 in the parse,
   0x82b3c in the mac loop; their slow paths and __asan_report_load1 calls are 0x8314c-0x83198 and 0x82b68-0x82b74)
   is a check of the token executor, which takes the not-taken edge and leaves a `range_addressable` obligation;
   each obligation is discharged by `obl_of_block` on the input block (tactic s0_obl), so no report branch is
   taken -- none is stepped over.

   Premises (Section e), each the hypothesis of the same name in lib/A/P_LLVMFuzzerTestOneInput.v, with its owner:
   TL, TLF, ML, FFL (a Theorem Labs lane, the glue); stack_malloc_8_sz (a Theorem Labs lane); ASHF8 (two Theorem Labs lanes).  The
   walk constants WK are bound by HWRLO / HWRHI (a Theorem Labs lane's text, verbatim) and by HWENT / HWEMP / HWSTK, which
   are the statement's HA_LLVMF, HA_EMPTY and HSTK in terms of WK; the composition discharges all five.  AR_laws
   is AR_laws_ok and stack_malloc_progressP is a field of ML (ENTRY-REVIEW.md R4); the two journal steps are
   a Theorem Labs lane's proved lemmas (a working branch d1cfd1a8204, lib/A/J_StackSzPf.v). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal SceneSyms SceneList SceneAddr SceneCode ScenePa ScenePaLib
SceneBase SceneFrame SceneRo SceneImg YC1g YC1h YC45 YC85 YC88 YC4b YC81 YC1i ACbf SceneACja SceneACjr ACj1.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import SceneAsanTop.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx J_StackSz P_check_step_frame P_LLVMFuzzerTestOneInput_seg.
(* A Theorem Labs lane (at d1cfd1a8204): the two caller-side journal steps J_StackSz.v states, PROVED. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import J_StackSzPf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h / the sink widening (a Theorem Labs lane, 2026-10-29 01:57Z): the sink head is a Section variable whose type is written
   fully qualified (lib/U/Reusable/YI16.v has the same short name), passed BY NAME to every term that takes it.  The
   composition instantiates it with scene's own head (lib/A/P_LLVMFuzzerTestOneInput.v:150-151, ofl_head 0x5f6e90). *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head). #[local] Existing Instance SK.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).

Section e.
Variable B : asyms.
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.

(* ---- the entry's symbolic state ------------------------------------------------------------------
   Atoms 0..31 are the entry registers; atom 32 is the shadow offset.  The regions are the machine stack
   below sp, the two GOT words the prologue reads (objects 1 and 0) and the two runtime cells they hold
   (objects 16 and 17): the shadow base and the use-after-return flag, whose value 1 is `al_const`'s
   (ENTRY-REVIEW.md item 5 / R4: the flag is read, never assumed). *)
Definition sc_extra : list word := [Z_to_bv 64 SHADOW_OFF].
Definition ELV (regs : bvmap 5 word) : env := Eimg (Ereg regs sc_extra).
Definition llvmf_regions : smem :=
[ stack_region 224; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 17); uar_cell_regionP (A_OBJ 17) ].
Definition llvmf_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 0);
(11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_llvmf : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms llvmf_regions None llvmf_facts.
Definition LVBx : sv := SOff 32 0.
Definition LVspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition llvmf_SH : list shent := [].

(* AR_laws is a theorem (Reusable/YG0q.v:803), not a hypothesis (ENTRY-REVIEW.md R4). *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma s0_entry : forall LLVMF_STK ly S W (regs : bvmap 5 word) mem md p n,
afn_pre SEGS B LLVMF_STK ly S W regs mem md [] ->
240 <= LLVMF_STK ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
4096 <= p -> p + n <= 140737479966720 -> 0 <= n < 2 ^ 26 ->
st_ok_pi SEGS VAL (ELV regs) ss_llvmf
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS)))
/\ sh_ok SEGS LVBx llvmf_SH (ELV regs) (mrestrict (w_H W) mem).
Proof.
intros LLVMF_STK ly S W regs mem md p n HPRE HSTK H10 H11 Hp4096 Hpceil Hn26.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 16 ltac:(lia)) as Hob16. pose proof (pa_obj_img 17 ltac:(lia)) as Hob17.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep. rewrite (pal_uar_cell B TL) in Hsep.
rewrite restrict_mkst_fx.
set (E := ELV regs).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs sc_extra) k)
by (intros k Hk; subst E; unfold ELV; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO : forall i, (i < 18)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst E; unfold ELV; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k w, ew E k = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some k) = w).
{ intros k w Hk Hw. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hw. }
assert (VO : forall i, (i < 18)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | pose proof (pa_val_range (A_OBJ i)); lia]. }
split.
- unfold ss_llvmf. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold llvmf_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VO 1%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
      [cbn [sv_denot]; rewrite (EO 16%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VO 16%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VO 0%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 17) 0) (VAL (A_OBJ 17)));
      [cbn [sv_denot]; rewrite (EO 17%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 17)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
    * rewrite (VO 17%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
  + apply pairwise_disjoint_of_extents.
    unfold llvmf_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VO 0%nat), (VO 1%nat), (VO 16%nat), (VO 17%nat) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 Hstk0 Hob0 Hob1 Hob16 Hob17 Hsep. clear. intros.
    rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
    repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok llvmf_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 Hstk0 Hal16 Hp4096 Hpceil Hn26. clear. unfold SHADOW_OFF. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, llvmf_SH. constructor.
Qed.

(* ---- the runtime contracts and framework laws this segment needs.  Each is the hypothesis of the same
   name in lib/A/P_LLVMFuzzerTestOneInput.v, with the owner that file names. ---- *)
(* A Theorem Labs lane: the glue's instances. *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.
(* A Theorem Labs lane (968ea35e8f5 proves it; this lane TAKES it). *)
Hypothesis stack_malloc_8_sz : astack_malloc_sz_realizes SEGS B PC_STACK_MALLOC_8 CID8.
(* Two Theorem Labs lanes: __asan_set_shadow_f8. *)
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
(* the two caller-side journal steps of lib/A/J_StackSz.v, proved by a Theorem Labs lane in lib/A/J_StackSzPf.v. *)
Let AJSM8 : @aj_stack_malloc_sz_at_stmt fx rc SK SEGS B :=
@aj_stack_malloc_sz_at fx rc SK SEGS B LAWS (pa_segs_low (L := scene_listing)) (pal_env B TL) ML
(ml_stack_malloc_progress _ ML).
Let AJSH : @aj_set_shadow_at_stmt fx rc SK SEGS B :=
@aj_set_shadow_at fx rc SK SEGS B LAWS (pa_segs_low (L := scene_listing)).

(* The side-stack entry of class 8 is the image's own: no PALibF field is needed for it. *)
Lemma s0_sm8 : SIGMA SS___asan_stack_malloc_8 = PC_STACK_MALLOC_8.
Proof. vm_compute. reflexivity. Qed.

(* gate 6h: the sink head is passed BY NAME to every term whose Section left it implicit. *)
Let RUN := @paj_run fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNTO := @paj_run_to fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNP := @SRr_run_pi_AJ fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNC := @SRr_run_pi_AJ_call fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNTOP := @SRr_run_to_pi_AJ fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let BR := paj_branch (PI := PI_scene).

(* The region based at atom b, cut to [lo, h) with only the chunks below h: what a call keeps of the frame
   shadow when it writes the shadow at and above offset h. *)
Definition s0_trunc (b : nat) (h : Z) (rs : smem) : smem :=
map (fun r => match YP09.r_base r with
| Some b' => if Nat.eqb b' b then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) h (YP09.r_wlo r) h
(List.filter (fun c => YP09.c_off c + YP09.c_len c <=? h) (YP09.r_chunks r)) else r
| None => r end) rs.
(* region_kept for a region off the image: the bytes are the same and, in the writable window only, presence
   is kept (the set-shadow post keeps presence of every byte outside the image). *)
Lemma s0_region_kept_off : forall E H (m m2 : word -> option byte) k b lo hi wlo whi cs,
bv_unsigned (ew E k) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m a -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some k) lo hi wlo whi cs).
Proof.
intros E H m m2 k b lo hi wlo whi cs Hk Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hk; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- apply writable_kept. apply Hp. exact Ha.
Qed.

(* An input byte at the current state is the entry state's byte (the journal keeps heap-block bytes), as
   cgif_file_fuzzer A/ACf9.v:489 PB_at_now. *)
Lemma s0_byte_now : forall STK sp0 ly S W mem md own ly3 S3 W3 mem3 md3 k p n i,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 [] ly S W mem md own ly3 S3 W3 mem3 md3 k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly3 S3) -> 0 < n -> 0 <= i < n ->
exists b, (0 <= b < 256 /\ val_mem SEGS (mrestrict (w_H W) mem) (p + i) 1 b) /\ aview SEGS (w_H W3) mem3 (p + i) = Some b.
Proof.
intros STK sp0 ly S W mem md own ly3 S3 W3 mem3 md3 k p n i HAR0 HJ Hin0 Hin3 Hn Hi.
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [lia | reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hin0) as (_ & _ & _ & _ & Hpres & _). rewrite Hrq in Hpres.
destruct (aview SEGS (w_H W) mem (p + i)) as [b|] eqn:Eb;
[| exfalso; exact (aview_some_of_apresent SEGS _ _ _ (proj1 (Hpres (p + i) ltac:(lia))) Eb)].
destruct (aview_byte SEGS _ _ _ b Eb) as (bb & _ & _ & Hb).
exists b. split.
- split; [exact Hb | apply val_mem1_of_aview; exact Eb].
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n i Hin0 Hin3); [exact Eb | rewrite Hrq; exact Hi | apply inFP_nil].
Qed.
(* The input-length cases of the parse: the code branches on n = 0 .. 4 and, in the 6-turn mac loop, on
   n = 5 .. 10; from n = 11 on every branch goes the same way. *)
Lemma s0_ncase : forall n, 0 <= n ->
n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ 11 <= n.
Proof. intros n Hn. lia. Qed.





(* A one-byte chunk of a region of the symbolic state is the byte in memory (a Theorem Labs lane's CheckGroupaWalk.v
   cg_chunk_aview, for any stored value: the byte is its low 8 bits). *)
Lemma s0_chunk_byte : forall E ss (H : word -> bool) msX i k b lo hi wlo whi cs od e,
st_ok SEGS E ss (restrict H msX) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some k) lo hi wlo whi cs) ->
bv_unsigned (ew E k) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
aview SEGS H (ms_mem msX) (b + od) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E ss H msX i k b lo hi wlo whi cs od e HS Hi Hb Hc.
pose proof (st_ok_region_nth E ss (restrict H msX) i _ HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (field_of_region_any E _ k b cs lo hi wlo whi od 1%N e HR Hb Hc ltac:(cbn; lia)) as V.
change (N.to_nat 1) with 1%nat in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.
(* Every region not based at atom b. *)
Definition s0_drop (b : nat) (rs : smem) : smem :=
List.filter (fun r => match YP09.r_base r with Some b' => negb (Nat.eqb b' b) | None => true end) rs.
(* The frame-shadow cells [0, 0x1c) as the 28 inline stores 0x82960-0x829d0 leave them. *)
Definition s0_sh0 (o : Z) : Z :=
if o <? 4 then 241 else if o <? 9 then 248 else if o <? 14 then 242 else if o <? 15 then 248
else if o <? 18 then 242 else if o <? 23 then 248 else 242.
(* The 1176 frame-shadow cells as the poison leaves them (before the mac unpoison store 0x82b1c). *)
Definition s0_shv (o : Z) : Z := if o <? 28 then s0_sh0 o else if o <? 1141 then 248 else 243.

(* An 8-byte chunk of a region of the symbolic state is the word in memory. *)
Lemma s0_chunk8 : forall E ss (H : word -> bool) msX i k b lo hi wlo whi cs od e v,
st_ok SEGS E ss (restrict H msX) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some k) lo hi wlo whi cs) ->
bv_unsigned (ew E k) = b -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
rdword (aview SEGS H (ms_mem msX)) (b + od) = Some v.
Proof.
intros E ss H msX i k b lo hi wlo whi cs od e v HS Hi Hb Hc He Hv.
pose proof (st_ok_region_nth E ss (restrict H msX) i _ HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (field_of_region E _ k b cs lo hi wlo whi od 8%N e v HR Hb Hc He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as V.
apply rdword_of_val_mem; [exact V | exact Hv].
Qed.
(* The read-only window and the image bytes are kept by the journal (YCbq.v:362-363). *)
Lemma s0_rod_kept : forall STK sp0 ly S W mem md own ly3 S3 W3 mem3 md3 k rlo rhi,
(forall a, rlo <= a < rhi -> in_img SEGS a) ->
ajournal SEGS B STK sp0 [] ly S W mem md own ly3 S3 W3 mem3 md3 k ->
arodata_okS SEGS B rlo rhi (aview SEGS (w_H W) mem) ->
arodata_okS SEGS B rlo rhi (aview SEGS (w_H W3) mem3).
Proof.
intros STK sp0 ly S W mem md own ly3 S3 W3 mem3 md3 k rlo rhi Hro HJ HR a Ha Hs He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fimg & _).
rewrite (Fimg a); [exact (HR a Ha Hs He) | | exact Hs | exact He |].
- destruct Ha as [(s & Hin & _ & Hr) | Hr]; [exists s; split; [exact Hin | exact Hr] | apply Hro; exact Hr].
- intros (r & Hr & _). destruct Hr.
Qed.
(* Byte arithmetic of the parse: the little-endian u16 and the two sign-extended halfwords. *)
Lemma s0_land_shl8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.land (Z.shiftl x 8) y = 0.
Proof.
intros x y Hx Hy. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases k 8) as [Hl|Hg].
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 y k); [apply Bool.andb_false_r | lia |].
  assert (Z.log2 y <= Z.log2 255) by (apply Z.log2_le_mono; lia). change (Z.log2 255) with 7 in H. lia.
Qed.
Lemma s0_lor8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = x * 256 + y.
Proof.
intros x y Hx Hy. rewrite <- Z.lxor_lor by (apply s0_land_shl8; lia).
rewrite <- Z.add_nocarry_lxor by (apply s0_land_shl8; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia.
Qed.
Lemma s0_lor48 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (x * 2 ^ 56) (y * 2 ^ 48) = (x * 256 + y) * 2 ^ 48.
Proof.
intros x y Hx Hy.
replace (x * 2 ^ 56) with (Z.shiftl (Z.shiftl x 8) 48) by (rewrite !Z.shiftl_mul_pow2 by lia; ring).
replace (y * 2 ^ 48) with (Z.shiftl y 48) by (rewrite Z.shiftl_mul_pow2 by lia; ring).
rewrite <- Z.shiftl_lor. rewrite s0_lor8 by lia. rewrite Z.shiftl_mul_pow2 by lia. ring.
Qed.
(* ---- byte arithmetic of the E parse, by exhaustion over the byte values (vm_compute); a Theorem Labs lane's AU S0
   (at 8b9208d286e, lib/AU/P_LLVMFuzzerTestOneInput_S0.v:151-164). ---- *)
Lemma s0_brute1 : forall f g : Z -> Z,
forallb (fun b => Z.eqb (f (Z.of_nat b)) (g (Z.of_nat b))) (seq 0 256) = true -> forall v, 0 <= v < 256 -> f v = g v.
Proof.
intros f g H v Hv. rewrite forallb_forall in H. specialize (H (Z.to_nat v) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.
Lemma s0_brute2 : forall f g : Z -> Z -> Z,
forallb (fun a => forallb (fun b => Z.eqb (f (Z.of_nat a) (Z.of_nat b)) (g (Z.of_nat a) (Z.of_nat b))) (seq 0 256)) (seq 0 256) = true ->
forall u v, 0 <= u < 256 -> 0 <= v < 256 -> f u v = g u v.
Proof.
intros f g H u v Hu Hv. rewrite forallb_forall in H. specialize (H (Z.to_nat u) ltac:(apply in_seq; lia)).
rewrite forallb_forall in H. specialize (H (Z.to_nat v) ltac:(apply in_seq; lia)).
rewrite !Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.

Lemma s0_swrap_hi : forall v, 0 <= v < 65536 ->
bv_swrap 64 (v * 2 ^ 48) = (if v <? 32768 then v else v - 65536) * 2 ^ 48.
Proof.
intros v Hv. rewrite swrap64_of_unsigned by (unfold M64; lia). unfold half64, M64.
destruct (Z.ltb_spec v 32768) as [Hl|Hg]; destruct (Z.ltb_spec (v * 2 ^ 48) (2 ^ 63)); lia.
Qed.
Lemma s0_sra48 : forall v, 0 <= v < 65536 ->
zcanon (Z.shiftr (bv_swrap 64 (v * 2 ^ 48)) 48) = sx16 v mod 2 ^ 64.
Proof.
intros v Hv. rewrite s0_swrap_hi by exact Hv. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
unfold zcanon, M64, sx16. reflexivity.
Qed.




(* The index of the first region of a list based at atom k. *)
Fixpoint s0_ridx (k : nat) (rs : smem) (i : nat) : nat :=
match rs with
| [] => i
| r :: rs' => match YP09.r_base r with
  | Some k' => if Nat.eqb k' k then i else s0_ridx k rs' (S i)
  | None => s0_ridx k rs' (S i) end
end.


(* ---- the cut C1 at 0x82b78, from what every input-length case of the walk establishes there ----
   The twelve cases of the parse (n = 0 .. 10 and n >= 11) end in the same machine shape: this lemma assembles
   cut_C1 once, from the journal, the frame's flag word and shadow cells, the save area, the four spills and the
   registers, and hands it to the next segment. *)
Lemma s0_c1 : forall WK (POST : world SEGS -> config -> Prop) ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n T
fpos S2 memF (regsF : bvmap 5 word) mdF (bs : Z -> Z) E0,
@sc_from_C1 fx rc SK SEGS B ameter_triv WK scene_geom_asan
(mkRTCX SEGS ly S W regs mem md p n fpos (32 * ((spZ regs - 224) / 32)) E0 T) POST ->
arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W) mem) ->
(forall a, sw_rlo WK <= a < sw_rhi WK -> in_img SEGS a) ->
@ajournal rc SK SEGS B (sw_stk WK) (spZ regs) [] ly S W mem md [(8, fpos)] ly S2 W memF mdF 0 ->
frames S2 = [(8, fpos)] -> ablocks B ly S2 = ablocks B ly S -> blocks_bytes S2 = blocks_bytes S ->
rdword (aview SEGS (w_H W) memF) (frame_addr ly 8 fpos + 16376) = Some (flag_addr ly 8 fpos) ->
(forall j, 0 <= j < 13 -> rdword (aview SEGS (w_H W) memF) (spZ regs - 8 - 8 * j)
= Some (bv_unsigned (getr regs (nth (Z.to_nat j) sc_saved_regs 0%bv)))) ->
(forall o, 0 <= o < 1176 -> o <> 14 ->
aview SEGS (w_H W) memF (SB + frame_addr ly 8 fpos / 8 + o) = Some (s0_shv o)) ->
aview SEGS (w_H W) memF (SB + frame_addr ly 8 fpos / 8 + 14) = Some 6 ->
(forall i, 0 <= i < 11 -> 0 <= bs i < 256 /\
(i < n -> 0 <= bs i < 256 /\ val_mem SEGS (mrestrict (w_H W) mem) (p + i) 1 (bs i)) /\ (n <= i -> bs i = 0)) ->
(forall j, 0 <= j < 6 -> aview SEGS (w_H W) memF (frame_addr ly 8 fpos + 112 + j) = Some (bs (5 + j))) ->
rdword (aview SEGS (w_H W) memF) (32 * ((spZ regs - 224) / 32) + 32) = Some (SB + frame_addr ly 8 fpos / 8 + 28) ->
rdword (aview SEGS (w_H W) memF) (32 * ((spZ regs - 224) / 32) + 40) = Some (frame_addr ly 8 fpos) ->
rdword (aview SEGS (w_H W) memF) (32 * ((spZ regs - 224) / 32) + 48) = Some (frame_addr ly 8 fpos + 112) ->
rdword (aview SEGS (w_H W) memF) (32 * ((spZ regs - 224) / 32) + 80) = Some (sx16 (bs 3 + 256 * bs 4) mod 2 ^ 64) ->
getr regsF 2%bv = w64 (32 * ((spZ regs - 224) / 32)) -> getr regsF 3%bv = w64 (as_gp B) -> getr regsF 4%bv = w64 (as_tp B) ->
getr regsF 8%bv = w64 (spZ regs) -> getr regsF 9%bv = w64 (32 * ((spZ regs - 224) / 32)) ->
getr regsF 23%bv = w64 (frame_addr ly 8 fpos) -> getr regsF 19%bv = w64 (SB + frame_addr ly 8 fpos / 8) ->
getr regsF 26%bv = w64 SHADOW_OFF ->
getr regsF 25%bv = w64 (frame_addr ly 8 fpos + 32) -> getr regsF 27%bv = w64 (frame_addr ly 8 fpos + 144) ->
getr regsF 15%bv = w64 (frame_addr ly 8 fpos + 224) ->
getr regsF 16%bv = w64 (bs 0) -> getr regsF 24%bv = w64 (bs 1 + 256 * bs 2) ->
getr regsF 21%bv = w64 (n - Z.min n 11) -> getr regsF 22%bv = w64 (p + Z.min n 11) ->
getr regsF 18%bv = w64 (sx16 (256 * bs 4) mod 2 ^ 64) ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 768)) memF (seg_rom SEGS)) mdF) POST.
Proof.
intros WK POST ly S W regs mem md p n T fpos S2 memF regsF mdF bs E0 KONT HROD HWKro HJ Hfrs Eab Hbb HFL HSAV SHV SH14
HIN HMAC S20 S28 S30 S50 R2 R3 R4 R8 R9 R23 R19 R26 R25 R27 R15 R16 R24 R21 R22 R18.
set (F := frame_addr ly 8 fpos) in *. set (FL := flag_addr ly 8 fpos) in *.
set (sp1 := 32 * ((spZ regs - 224) / 32)) in *.
assert (Hfin : In (8, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 8 fpos (proj1 HJ) Hfin) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 8) with 16384 in HFpres, HFSpres. change (16384 / 8) with 2048 in HFSpres. fold F in HFal, HFpres, HFSpres.
assert (HFmod8 : F mod 8 = 0).
{ apply Z.mod_divide in HFal; [|lia]. destruct HFal as [q Hq]. rewrite Hq. replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult. }
assert (Hpc1 : sg_pc_c1 scene_geom_asan = BASE + 768)
by (unfold scene_geom_asan; cbn [sg_pc_c1]; unfold AF_LLVMFuzzerTestOneInput, SEG_C1_off; lia).
replace (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 768)) memF (seg_rom SEGS)) mdF)
with (cfg_at SEGS (sg_pc_c1 scene_geom_asan) regsF memF mdF) by (unfold cfg_at; rewrite Hpc1; reflexivity).
apply (KONT ly S2 W regsF memF mdF bs).
unfold cut_C1.
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_T].
split.
{ unfold sc_j. cbn [c_ly c_S c_W c_regs c_mem c_md c_fpos c_T sg_cid scene_geom_asan].
  split; [exact HJ|]. split; [exact Hfrs | exact I]. }
split; [exact Eab|]. split; [exact Hbb|].
split.
{ unfold sc_frame, sc_F, rt_F, rt_FL. cbn [c_ly c_fpos sg_cid scene_geom_asan]. fold F FL.
  change (fs_frame_bytes 8) with 16384. change (16384 / 8) with 2048.
  split; [| split].
  - replace (F + 16384 - 8) with (F + 16376) by lia. exact HFL.
  - intros a Ha. exact (proj1 (HFpres a Ha)).
  - intros a Ha. unfold shadow_addr in *. rewrite <- SB_SHADOW_OFF in *.
    replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia.
    exact (proj1 (HFSpres (a - (SB + F / 8)) ltac:(lia))). }
split; [exact HSAV|].
assert (SHR : forall lo hi v, 0 <= lo -> hi <= 1176 -> (forall o, lo <= o < hi -> o <> 14 /\ s0_shv o = v) ->
  sc_shr SEGS scene_geom_asan (mkRTCX SEGS ly S W regs mem md p n fpos sp1 E0 T) W memF lo hi v).
{ intros lo hi v Hlo Hhi Hv o Ho. unfold sc_F, rt_F. cbn [c_ly c_fpos sg_cid scene_geom_asan]. fold F.
  unfold shadow_addr. rewrite <- SB_SHADOW_OFF. destruct (Hv o Ho) as [Hne Hval]. rewrite <- Hval. apply SHV; lia. }
assert (SHC : forall lo hi v, (forall o, lo <= o < hi -> s0_shv o = v) -> forall o, lo <= o < hi -> s0_shv o = v) by auto.
split.
{ unfold sc_shbg. cbn [sg_sh_bg scene_geom_asan].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; apply SHR; try lia;
  (intros o Ho; unfold s0_shv, s0_sh0; split; [lia|
   repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y); try lia end; reflexivity]). }
split.
{ cbn [sg_sh_blki_lo sg_sh_blki_hi scene_geom_asan]. apply SHR; try lia.
  intros o Ho; unfold s0_shv, s0_sh0; split; [lia|].
  repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y); try lia end; reflexivity. }
split.
{ cbn [sg_sh_blk_lo sg_sh_blk_hi scene_geom_asan]. apply SHR; try lia.
  intros o Ho; unfold s0_shv, s0_sh0; split; [lia|].
  repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y); try lia end; reflexivity. }
split.
{ unfold sc_open, sc_F, rt_F. cbn [c_ly c_fpos sg_cid sg_off_mac sg_mac_n scene_geom_asan]. fold F.
  split; [rewrite Z.add_mod, HFmod8 by lia; reflexivity|]. split; [lia|].
  intros i Hi. change ((6 + 7) / 8) with 1 in Hi. assert (i = 0) as -> by lia. cbn.
  unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  replace ((F + 112) / 8) with (F / 8 + 14).
  - rewrite Z.add_0_r, Z.add_assoc. exact SH14.
  - apply Z.mod_divide in HFmod8; [|lia]. destruct HFmod8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 112) with ((q + 14) * 8) by lia. rewrite !Z.div_mul by lia. reflexivity. }
split.
{ unfold sc_img. cbn [c_sp1]. split; [unfold spZ; rewrite R2; apply unsigned_lit_small|].
  - unfold sp1. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
    unfold astk_ok in HSTKOK. pose proof asan_consts as (C1 & _).
    pose proof (Z.div_pos (spZ regs - 224) 32 ltac:(lia) ltac:(lia)).
    pose proof (Z.mul_div_le (spZ regs - 224) 32 ltac:(lia)). lia.
  - split; [exact R3|]. split; [exact R4|]. eapply s0_rod_kept; [exact HWKro | exact HJ | exact HROD]. }
split.
{ unfold sc_in, sc_PB. cbn [c_n c_p c_W c_mem]. exact HIN. }
split.
{ unfold sc_F, rt_F. cbn [c_ly c_fpos sg_cid sg_off_mac scene_geom_asan]. fold F. unfold garr8, sc_macb.
  intros j Hj. cbn [length] in Hj.
  assert (Hj' : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5)%nat) by lia.
  destruct (HIN 5 ltac:(lia)) as [B5 _]. destruct (HIN 6 ltac:(lia)) as [B6 _]. destruct (HIN 7 ltac:(lia)) as [B7 _].
  destruct (HIN 8 ltac:(lia)) as [B8 _]. destruct (HIN 9 ltac:(lia)) as [B9 _]. destruct (HIN 10 ltac:(lia)) as [B10 _].
  repeat (destruct Hj' as [-> | Hj']); [..| subst j]; cbn [nth Z.of_nat];
  (lazymatch goal with |- val_mem _ _ (_ + 112 + ?z) _ _ /\ _ =>
   split; [apply (proj1 (val_mem1_of_aview SEGS _ _ _ _ (HMAC z ltac:(lia)))) | lia] end). }
unfold vat. cbn [sg1_sp0 sg1_sp1 sg1_F sg1_Fsp sg1_shF sg1_shbase sg1_blki sg1_blk sg1_expect sg1_mac sg1_shexp
sg1_flags sg1_u16 sg1_rest sg1_cur sg1_step sg1_s7v scene_geom_asan].
unfold sc_F, rt_F, sc_flags, sc_u16, sc_rest, sc_cur, sc_step, sc_s7v, shadow_addr.
cbn [c_ly c_fpos c_n c_p sg_cid sg_off_blki sg_off_blk sg_off_expect sg_off_mac scene_geom_asan]. fold F.
rewrite <- SB_SHADOW_OFF. change (224 / 8) with 28.
unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s5, RV_s6, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11, RV_a5, RV_a6.
repeat split; first [ assumption | (replace (sp1 + 48) with (sp1 + 48) by reflexivity; assumption) ].
Qed.
End e.

(* seg_S0_stmt (lib/A/P_LLVMFuzzerTestOneInput_seg.v) on the input lengths n with C n. *)
Definition s0_case_stmt (B : asyms) (WK : swalk) (C : Z -> Prop) : Prop :=
forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n T (POST : world SEGS -> config -> Prop),
C n ->
sc_base0 SEGS B ameter_triv WK ly S W regs mem md p n T ->
(forall fpos E0,
@sc_from_C1 fx rc SK SEGS B ameter_triv WK scene_geom_asan
(mkRTCX SEGS ly S W regs mem md p n fpos (32 * ((spZ regs - 224) / 32)) E0 T) POST) ->
SRr SEGS W (cfg_at SEGS (sw_entry WK) regs mem md) POST.

(* The input-length cases of s0_ncase together are seg_S0_stmt: sc_base0 gives 0 <= n. *)
Lemma s0_cases : forall (B : asyms) (WK : swalk),
s0_case_stmt B WK (fun n => n = 0) ->
s0_case_stmt B WK (fun n => n = 1) ->
s0_case_stmt B WK (fun n => n = 2) ->
s0_case_stmt B WK (fun n => n = 3) ->
s0_case_stmt B WK (fun n => n = 4) ->
s0_case_stmt B WK (fun n => n = 5) ->
s0_case_stmt B WK (fun n => n = 6) ->
s0_case_stmt B WK (fun n => n = 7) ->
s0_case_stmt B WK (fun n => n = 8) ->
s0_case_stmt B WK (fun n => n = 9) ->
s0_case_stmt B WK (fun n => n = 10) ->
s0_case_stmt B WK (fun n => 11 <= n) ->
@seg_S0_stmt fx rc SK SEGS B ameter_triv WK scene_geom_asan.
Proof.
intros B WK C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11.
unfold seg_S0_stmt. intros ly S W regs mem md p n T POST HPRE0 KONT.
pose proof HPRE0 as (_ & _ & _ & _ & Hpn & _).
assert (Hn0 : 0 <= n) by (destruct Hpn as [[-> _] | [Hn' _]]; lia).
destruct (s0_ncase n Hn0) as [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]]]]]]]];
[ exact (C0 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C1 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C2 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C3 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C4 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C5 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C6 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C7 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C8 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C9 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C10 ly S W regs mem md p n T POST Hc HPRE0 KONT)
| exact (C11 ly S W regs mem md p n T POST Hc HPRE0 KONT)
].
Qed.
End b.

(* A hypothesis lia does not see (lia case-splits every disjunction and `mod` fact in the context). *)
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
| H : _ \/ _ |- _ => apply rs_hide in H
| H : _ mod _ = _ |- _ => apply rs_hide in H end.

(* ---- the Ltacs of the walk (lines 256-269, 271-282, 284-296, 298-309, 331-339, 340-346, 412-417, 418-422, 423-427, 442-444, 445-450, 452-457, 459-465, 475-476, 477-479, 480-481, 483-488 of the one-file version) ---- *)
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
(* SceneACja's awrFL closes the machine-stack window with `clear; lia`, which needs the stack budget to be a
   literal; here it is the contract's parameter `sw_stk WK`, so the stack case is given as the `hd` rule with
   that bound in scope. *)
Ltac s0_awr_stk HSTKW AG :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
[reflexivity | evalE AG | clear - HSTKW; cbn; unfold ASTACK, ESTACK in *; zconst_lits; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hs1 : sp0 - _ <= ?s1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (s1 - sp0));
[reflexivity | evalE AG | clear - Hs1 HSTKW; cbn; unfold ASTACK, ESTACK in *; zconst_lits; lia
| clear - Hs1; cbn; lia |] end
end.
(* keptFL closes the two machine-stack regions with `lia` after unfolding ASTACK in the GOAL only; the stack
   budget here is the parameter `sw_stk WK`, so those two cases are given as the `hd` rule with ASTACK unfolded
   in the hypothesis too. *)
Ltac s0_kept_stk HK HJx AG HSTKW :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | evalE AG
| unfold ESTACK, ASTACK in *; zconst_lits; lia | unfold ESTACK, ASTACK in *; zconst_lits; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _); [exact HK | exact HJx | evalE AG
| unfold ESTACK, ASTACK in *; zconst_lits; lia | unfold ESTACK, ASTACK in *; zconst_lits; lia | lia | lia | lia]
end.
(* Across an intrinsic that writes only [q, q + n) (the set-shadow post): the four off-image regions (the frame
   shadow, the frame, the spill area, the machine stack) are kept byte by byte, and presence is kept off the
   image.  The image regions are keptFL's. *)
Ltac s0_kept_sh HKO HPR AG :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?k) _ _ _ _ _) =>
lazymatch k with 529%nat => idtac | 516%nat => idtac | 60%nat => idtac | 2%nat => idtac end;
eapply s0_region_kept_off;
[ evalE AG
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HKO; [lia | unfold off_img, SB in *; lia]
| let a := fresh "a" in let Ha := fresh "Ha" in let Hi := fresh "Hi" in
  intros a Ha; apply HPR; [lia | intros Hi; pose proof (pa_img_range a Hi); unfold off_img, SB in *; lia] ]
end.
(* An ASan check on an input byte: ACbf's obl_blk, with the block's request size rewritten by Hrq (the input
   length is a variable here). *)
Ltac s0_obl HJx HEn HEbx Hin Hrq :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?k ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex k p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex k p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | rewrite Hrq; lia ] end end end.
(* What a run leaves: every byte outside the run's writable windows (a Theorem Labs lane's CheckGroupaWalk.v cg_win). *)
Ltac s0_win HFr Zs KN AG :=
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zs HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
[injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; evalE AG; intros Hrr; cbv beta; unfold SB in *; lia|]);
destruct Hin)) as KN.
(* A one-byte chunk fact of region i of HS, at the offset the goal names. *)
Ltac s0_chunk_at HS i AG :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msX) =>
eapply eq_trans;
[ eapply (s0_chunk_byte Ex (abs_ss VAL ssx) Hh msX i);
  [ exact HS | reflexivity | evalE AG | cbn; repeat (first [left; reflexivity | right]) ]
| reflexivity ] end.
(* A closed equation in the bytes x (and y), decided by exhaustion. *)
Ltac s0_brute1_tac x Rx :=
lazymatch goal with |- ?L = ?R =>
let f := eval pattern x in L in let g := eval pattern x in R in
lazymatch f with ?F x => lazymatch g with ?G x =>
exact (s0_brute1 F G ltac:(vm_compute; reflexivity) x Rx) end end end.
Ltac s0_brute2_tac x y Rx Ry :=
lazymatch goal with |- ?L = ?R =>
let f := eval pattern x, y in L in let g := eval pattern x, y in R in
lazymatch f with ?F x y => lazymatch g with ?G x y =>
exact (s0_brute2 F G ltac:(vm_compute; reflexivity) x y Rx Ry) end end end.
(* U of a symbolic value whose atoms are input bytes with known values. *)
Ltac s0_Ubytes :=
rewrite ?U_SAlu, ?U_SLit;
repeat match goal with |- context [U ?Ex (SOff ?k 0)] =>
match goal with Hk : ew Ex k = Z_to_bv 64 ?v |- _ => rewrite (U_atom Ex k v Hk) by lia end end.
(* sv_denot of a symbolic value whose atoms the context knows. *)
Ltac s0_den AG := cbn [sv_denot]; rewrite ?Z.add_0_r; evalE AG;
try (rewrite !Z_to_bv_bv_unsigned; reflexivity); try reflexivity; try (f_equal; lia).
(* A register or spill value at C1: the atoms of the entry registers are rewritten to the entry registers (EE),
   then both sides are compared as words. *)
Ltac s0_rc AG EE := cbn [sv_denot]; rewrite ?Z.add_0_r; evalE AG;
rewrite ?(EE 2%nat 2%bv eq_refl), ?(EE 3%nat 3%bv eq_refl), ?(EE 4%nat 4%bv eq_refl);
unfold w64, spZ; rewrite ?Z_to_bv_bv_unsigned;
first [ reflexivity | assumption | (f_equal; lia) ].
(* After a run the model is `with_vm_backing (m_vm_lazy md) mat md`, which holds md twice: name it, so it does not
   double on every run (a Theorem Labs lane). *)
Ltac s0_md := try (lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
lazymatch mdx with
| with_vm_backing _ _ _ => let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv
| _ => idtac end end).
(* The disjointness conjuncts of the two frame regions.  `zone_lia` cannot normalise the literal division
   `16384 / 8` that `change (fs_frame_bytes 8) with 16384` leaves in the shadow region's span, and the frame's
   own position needs the application-range disjunction of `in_app`. *)
Ltac s0_disj :=
first [ zone_lia
| change (16384 / 8) with 2048; zone_lia
| change (16384 / 8) with 2048; unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac s0_idx HS k := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
let i := eval vm_compute in (s0_ridx k (ss_mem ss) 0) in constr:(i) end.
(* An 8-byte / 1-byte chunk of the region of HS based at atom k; the value and range premises are left. *)
Ltac s0_c8 HS AG k := let i := s0_idx HS k in eapply (s0_chunk8 _ _ _ _ i);
[ exact HS | reflexivity | evalE AG | cbn; repeat (first [left; reflexivity | right]) | idtac | idtac ].
Ltac s0_cb HS AG k := let i := s0_idx HS k in eapply (s0_chunk_byte _ _ _ _ i);
[ exact HS | reflexivity | evalE AG | cbn; repeat (first [left; reflexivity | right]) ].
(* A register of HS as the symbolic value the state holds, not normalised (prreg normalises sv_denot away). *)
Ltac s0_preg HS r Hr :=
lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr end.

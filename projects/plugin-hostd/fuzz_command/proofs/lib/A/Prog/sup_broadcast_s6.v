(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry of plugin-hostd/fuzz_command's sup_broadcast walk (0x8afa0), in the
   form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v: the symbolic state at the entry (the own 32-byte frame, the
   GOT word 0xa63f0 and the shadow-base cell 0xb10b8 it names, and g_rec's ncalls field holding n). The head of the
   walk reads ncalls and either records in the table's next slot (n < 16, sup_broadcast_s7.v) or frees the spill's
   arguments (n = 16, sup_broadcast_s8.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaArt CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_broadcast_c sup_broadcast_s1 sup_broadcast_s5.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at the entry: the own frame (written), the GOT word and the shadow-base cell (read), and
   g_rec's ncalls field, which the table arm writes *)
Definition sbe_ncalls (n : Z) : YP09.region :=
YP09.mkRegion (Some SB_GREC) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SLit n))].
Definition sbe_regions (n : Z) : smem := [stack_region 32; got_regionP; bcell_regionP 32; sbe_ncalls n].
Definition sbe_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB_SB SB_SB 0)] [] [].
Definition ss_sbe (n : Z) : sstate := mkSS AF_sup_broadcast sr_atoms (sbe_regions n) None sbe_facts.
Definition sbe_Bx : sv := SOff 32 0.
Definition sbe_SH : list shent := [].
Definition sbe_Bspan : Z * Z := (SB_SB, SB_SB + 2 ^ 44 - 1).
Definition sbe_extra : list word := [Z_to_bv 64 SB_SB].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* the program's statics are writable (YCbq.v's prog_rw, one of the walk hypotheses) *)
Hypothesis PRW : prog_rw SEGS B.

Lemma sbe_obj : VAL SB_GREC = A_G_REC /\ VAL SB_SPILL = A_REC_SPILL /\ VAL (A_OBJ 0) = 0xa63f0 /\ VAL (A_OBJ 12) = 0xb10b8.
Proof.
split; [exact (VOBJS 44%nat ltac:(vm_compute; lia))|].
split; [exact (VOBJS 51%nat ltac:(vm_compute; lia))|].
split; [exact (VOBJS 0%nat ltac:(vm_compute; lia)) | exact (VOBJS 12%nat ltac:(vm_compute; lia))].
Qed.

(* the entry's symbolic state *)
Lemma sbe_entry : forall ly S (W : world SEGS) regs mem md ch n,
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs sbe_extra)) (ss_sbe n)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_broadcast)) mem (seg_rom SEGS))) /\
sh_ok SEGS sbe_Bx sbe_SH (Eimg (Ereg regs sbe_extra)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch n HPRE Hn Hn16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct sbe_obj as (Vgrec & Vspill & V0 & V12).
set (E := Eimg (Ereg regs sbe_extra)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v)
  by (intros m v Hm Hv; cbn [base_val]; rewrite Hm; apply unsigned_lit_small; exact Hv).
assert (EO : forall m, (A_TEXT <= m < A_LIM)%nat -> ew E m = Z_to_bv 64 (VAL m))
  by (intros m Hm; subst E; apply Eimg_img; exact Hm).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
split.
- rewrite restrict_mkst_fx. unfold ss_sbe. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sbe_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stack_region, got_regionP, bcell_regionP, sbe_ncalls;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. assert (SUP_BROADCAST_STK = 16592) by reflexivity. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EO (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(rewrite V0; lia)).
      split; [rewrite V0; lia|]. split; [rewrite V0; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [ cbn [sv_denot]; rewrite (EO (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V12; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) (EO (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(rewrite V12; lia)).
      split; [rewrite V12; lia|]. split; [rewrite V12; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 sbe_Bx SB_SB);
      [ cbn [sv_denot sbe_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_SB; lia | lia |].
      rewrite Z.add_0_r. change SB_SB with SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB SB_GREC (VAL SB_GREC) (EO SB_GREC ltac:(unfold SB_GREC, A_OBJ, A_TEXT, A_LIM; lia)) ltac:(rewrite Vgrec; unfold A_G_REC; lia)).
      rewrite Vgrec. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split.
      -- intros o Ho. apply PRW. apply (HPROG B HB).
         exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
      -- constructor; [|constructor].
         apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SLit n) n); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
         change (N.to_nat 4) with 4%nat. apply sb_val_mem_of_aval. exact Hn.
  + apply pairwise_disjoint_of_extents. unfold sbe_regions, stack_region, got_regionP, bcell_regionP, sbe_ncalls, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EO (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(rewrite V0; lia)).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) (EO (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(rewrite V12; lia)).
    rewrite (VB SB_GREC (VAL SB_GREC) (EO SB_GREC ltac:(unfold SB_GREC, A_OBJ, A_TEXT, A_LIM; lia)) ltac:(rewrite Vgrec; unfold A_G_REC; lia)).
    cbn [base_val]. rewrite Usp, V0, V12, Vgrec.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC.
    assert (WSTK : SUP_BROADCAST_STK = 16592) by reflexivity.
    revert Hslo Hceil Hshi H47 C1 WSTK. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [sbe_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SB_SB; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. unfold SB_SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, sbe_SH. apply Forall_nil.
Qed.

End e.
End f.
End d.

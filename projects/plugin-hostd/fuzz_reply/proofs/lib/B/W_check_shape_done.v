(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) walk of fuzz_reply's check_shape_done, ported from
   lib/A/W_check_shape_done.v (a working branch), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v and lib/A/ACbk.v. *)
(* check_shape_done(n) at 0x85a5c (image B) loads g_nout and aborts unless n is its value.  Image B's body is
   image A's (0x85734) instruction for instruction: UBSan adds no check here, only the pc-relative operands move.
   The walk runs the ten instructions symbolically over B's relocatable listing (lib/B/W_listing.v), splits at the
   one branch, and refutes the abort arm from the contract's functional half. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_journal W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x.
(* route R: a Theorem Labs lane's contract twins aleaf_post_xR / csd_spec_xR (W_contract_srlf_xR.v, NAMES.md (sha256 4a0eb3e6fe06; internal record)) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_check_shape_done : Z := AF_fr_check_shape_done.
Definition A_check_shape_doneP : Z := BASE + A_check_shape_done.
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): check_shape_done over any allocator relation
   ARx with its laws, stated as W_contract_x.csd_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl /
   LAWS (the generic relation) and HP0 (the unit's hidden-head set is empty in every ARx state: fuzz_reply calls no
   poison routine; a Theorem Labs lane's ruling).  This leaf reads no heap block, so HP0 goes unused and is not in the theorem. ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* errno's placement (image bytes below kLowMemEnd) is PALib's pal_env: the bound aleaf_post_x's errno conjunct needs *)
Hypothesis TL : PALib B.
Let HG0 : gx_ok SEGS B [] := gx_ok_nil SEGS B.
Let RUN := paj_run_x_x B PST ARx LAWS [] HG0 0 [].
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx [] 0 []).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bx : sv := SOff 33 0.
Definition csd_regions : smem :=
[ stack_region CSD_STK;
YP09.mkRegion (Some A_g_nout) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
Definition csd_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_csd : sstate := mkSS A_check_shape_done sr_atoms csd_regions None csd_facts.
Definition csd_SH : list shent := [].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition csd_extra (n : Z) : list word := map (Z_to_bv 64) [n; SB].
Lemma csd_entry_x : forall W ly S Hp regs mem md ch n,
afn_pre_x SEGS B ARx CSD_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 n ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (csd_extra n))) ss_csd
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_shape_doneP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx csd_SH (Eimg (Ereg regs (csd_extra n))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch n HPRE H10 Rn Mn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSD_STK = 16) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (csd_extra n))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eno : ew E A_g_nout = Z_to_bv 64 (VAL A_g_nout)) by (subst E; apply Eimg_img; unfold A_g_nout, A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HnoR. change (A_OBJ 12) with A_g_nout in HnoR.
pose proof (pa_val_range A_g_nout) as HnoV.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_csd, A_check_shape_doneP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold csd_regions, stack_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB A_g_nout (VAL A_g_nout) Eno) by (pose proof (pa_val_range A_g_nout); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_nout) 0 8 (SOff 32 0) n);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mn.
+ apply pairwise_disjoint_of_extents. unfold csd_regions, stack_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB A_g_nout (VAL A_g_nout) Eno) by (pose proof (pa_val_range A_g_nout); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HnoR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [csd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Rn. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, csd_SH. constructor.
Qed.
Theorem pb_check_shape_done_x : csd_spec_x B PST ARx A_check_shape_doneP.
Proof.
intros W ly S Hp regs mem md ch n HPRE H10 Rn Mn.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (csd_entry_x W ly S Hp regs mem md ch n HPRE H10 Rn Mn) as [HS SHOK].
assert (HJ : AJG CSD_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem md 0)
by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx CSD_STK [] ly S Hp W regs mem md ch HPRE)).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs (csd_extra n))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (csd_extra n)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_check_shape_doneP) with (Z_to_bv 64 A_check_shape_doneP).
unfold A_check_shape_doneP, A_check_shape_done.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* the abort arm: a0 <> g_nout, which the contract's functional half refutes *)
exfalso. rewrite branch_ne_U, (U_atom E 10 n E10), (U_atom E 32 n E32) in Hc by lia.
cbn [negb] in Hc. apply (proj1 (Bool.negb_true_iff _)) in Hc. apply (proj1 (Z.eqb_neq _ _)) in Hc.
exact (Hc eq_refl).
-
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleaf_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs). apply ajournal_gx_nil_x. exact HJ.
+ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (csd_extra n) HS); [exact HAE | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, E10. reflexivity.
+ intros a Ha. cbn [ms_mem]. pres_chain.
(* errno: an image byte below kLowMemEnd, so outside the frame both runs write *)
+ intros jj Hjj. cbn [ms_mem].
  pose proof (pal_env B TL) as ((He0 & He1) & _). pose proof asan_consts as (C1 & _).
  pose proof Hstk as (_ & _ & Hc1 & Hc2 & _). unfold kLowMemEnd in He1. unfold CSD_STK in Hc2.
  transitivity (aview SEGS (w_H W) (ms_mem ms) (as_errno B + jj)).
  * lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf) end; [lia|].
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia|]).
    destruct Hin.
  * lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) mem) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf) end; [lia|].
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia|]).
    destruct Hin.
Qed.

(* ---- route R (group G7-leaf-AB, for a Theorem Labs lane's top_x at R): pb_check_shape_done_x at a world relation R, a LIFT
   with no re-proof.  The strict SRr run becomes SRrG SEGS R by SRr_SRrG (WLE_R), and the post's journal
   (aleaf_post_x -> aleaf_post_xR) goes to R by ajournal_xR_mono; W_contract_srlf_xR.v csd_spec_xR_of_x is those
   two steps. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Theorem pb_check_shape_done_xR : csd_spec_xR B PST ARx R A_check_shape_doneP.
Proof. apply (csd_spec_xR_of_x B PST ARx R WLE_R). exact pb_check_shape_done_x. Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_check_shape_done's statement is the AR
   walk's, byte-identical, now a corollary of pb_check_shape_done_x at ARx := ARi0 (cgif's AR with the head set
   empty), PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's ruling (a)) in place of LAWS: the
   instance builds it once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridge is W_contract_x
   csd_spec_x_AR0. ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Theorem pb_check_shape_done : csd_spec B A_check_shape_doneP.
Proof.
apply csd_spec_x_AR0.
eapply pb_check_shape_done_x; eassumption.
Qed.
End cAR.
End b.
End a.

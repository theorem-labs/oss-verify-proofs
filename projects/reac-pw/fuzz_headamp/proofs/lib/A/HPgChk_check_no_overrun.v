(* check_no_overrun 0x83e3c of fuzz_headamp.asan (unstripped sha256
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a; the pinned f3e0669d2819 has the same loaded
   bytes except .note.gnu.build-id), the image-A walk against lib/A/HPgCSpec.v's hd_check_no_overrun_specX. Proves function check_no_overrun
   (written new; the plumbing is lib/A/HPgChkBase.v).

   THE CODE (43 words, fuzz_headamp.c:183-192):
     0x83e3c addi sp,sp,-0x10; sd ra,8(sp); 0x83e44 auipc a1,0x18; ld a1,0x52c(a1) (the .got word 0x9c370);
     ld a2,0(a1) (the shadow-offset cell: 0x7fff8000); then three times, for g, g + 1, g + 2:
       srli; add (the shadow byte's address); lb (0x83e58 / 0x83e78 / 0x83e98); bnez (to the slow arms 0x83ec0 /
       0x83ecc / 0x83edc: `andi u,x,7; blt u,t,back`, then the report call); lbu (0x83e60 / 0x83e80 / 0x83ea0);
       addi a3,zero,0xa5; bne (to 0x83eb8);
     0x83eac ld ra,8(sp); addi sp,sp,0x10; 0x83eb4 ret; 0x83eb8 jal __asan_handle_no_return; jal abort.
   The only store is `sd ra,8(sp)` into the save slot [sp - 16, sp).
   WHY THE FAILURE BRANCH IS UNREACHABLE: the entry state holds the three bytes at g (a0) as the literal 0xa5 (the
   contract's garr8 premise), so the engine decides each `bne` at 0x83e68 / 0x83e88 / 0x83ea8 as not taken and the
   jal at 0x83eb8 is never stepped. WHY NO REPORT CALL IS REACHED: the shadow entry [g, g + 3) (from the contract's
   range_addressable and hd_app_rng premises) covers each checked byte, so the token engine continues at the `lbu`
   on both arms of each `bnez`, the slow arm included (it is live when g's granule is partial). One run reaches the
   `ret`. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgChkBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_CHECK_NO_OVERRUN : Z := 0x83e3c.
(* the 43 words 0x83e3c .. 0x83ee4 *)
Definition no_tbl : ctable := build_table rsegs A_CHECK_NO_OVERRUN 43 TEmpty.
Lemma no_tbl_ok : table_ok rsegs no_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_NO_OVERRUN. lia. Qed.

(* the three guard bytes at g (env slot 10), each the literal 0xa5 *)
Definition no_rs : smem :=
[hc_data 10 0 3 [YP09.mkChunk 0 (CVal 1 (SLit 0xa5)); YP09.mkChunk 1 (CVal 1 (SLit 0xa5)); YP09.mkChunk 2 (CVal 1 (SLit 0xa5))]].
Definition no_fs : list (nat * afact) := [hc_pfact 10 0].
(* the shadow entry: the three bytes from g are addressable *)
Definition no_SH : list shent := [mkSHE 10 0 3].
Lemma no_guard_nth : forall j, (j < 3)%nat -> nth j (hd_zbytes (repeat GUARD_BYTE 3)) 0 = 0xa5.
Proof. intros j Hj. destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia]. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HC_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HC_SH_CELL.

Theorem hd_check_no_overrun_A : hd_check_no_overrun_specX rsegs B MT A_CHECK_NO_OVERRUN.
Proof using MTL HBgot HBcell.
unfold hd_check_no_overrun_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 Hg Hsh Hoff (Happ & Himg).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hc_wx as Hwx. pose proof hc_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
destruct (hc_app_fact g 3 Happ ltac:(lia)) as (Hg0 & Hg1 & Hg2).
destruct (hc_app_apart g 3 Himg ltac:(lia)) as [Dgot Dcell].
unfold ASAN_CEIL in Hg1, Hg2.
unfold T_check_STK in Hwlo.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpr : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia).
assert (G : forall j, (j < 3)%nat -> val_mem rsegs (mrestrict (w_H W) memc) (g + Z.of_nat j) 1 0xa5).
{ intros j Hj. destruct (Hg j ltac:(unfold hd_zbytes; rewrite length_map, repeat_length; exact Hj)) as [Gv _].
  rewrite (no_guard_nth j Hj) in Gv. exact Gv. }
clear Hg.
remember (Ereg regs (hc_extra [])) as E eqn:HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = g)
by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; apply unsigned_lit_small; unfold HC_PHI in Hg2; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; apply hc_E32).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (HS : st_ok rsegs E (ss_hc A_CHECK_NO_OVERRUN [] no_rs no_fs)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_NO_OVERRUN) memc (seg_rom rsegs)))).
{ subst E. apply (hc_entry A_CHECK_NO_OVERRUN [] [] no_rs no_fs W regs memc ltac:(unfold A_CHECK_NO_OVERRUN; lia) (Forall_nil _)
    Hpr Hsp Kgot Kcell).
  - vm_compute. reflexivity.
  - unfold no_rs. apply Forall_cons; [|apply Forall_nil].
    apply (hc_data_ok _ _ 10 g 0 3 _ E10); [lia | lia |].
    repeat apply Forall_cons; try apply Forall_nil;
    (apply (hc_chunk1 _ _ g _ (SLit 0xa5) 0xa5 eq_refl); [lia|]).
    + exact (G 0%nat ltac:(lia)).
    + exact (G 1%nat ltac:(lia)).
    + exact (G 2%nat ltac:(lia)).
  - unfold hc_base_regions, no_rs, hc_stack_region, hc_got_region, hc_cell_region, hc_data, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold HC_GOT_SH, HC_SH_CELL in *. repeat split; lia.
  - cbn [atoms_ok no_fs hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r. unfold hc_SB, SHADOW_OFF, HC_PHI in *.
    repeat split; lia. }
assert (SHOK : sh_ok rsegs hc_Bx no_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, no_SH. apply Forall_cons; [|apply Forall_nil].
  apply (hc_shent (w_H W) memc E 10 g 0 3); [rewrite Z.add_0_r; exact Hsh | rewrite Z.add_0_r; exact Happ | exact E32 | exact E10 | lia]. }
assert (HAE : env_agree 32 (Ereg regs (hc_extra [])) E) by (subst E; apply env_agree_refl).
clear HE.
rename Usp into B2.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_CHECK_NO_OVERRUN) with (Z_to_bv 64 A_CHECK_NO_OVERRUN).
(* 0x83e3c .. 0x83eb0: the three checks continue at their loads, the three bytes are 0xa5; stop at 0x83eb4 ret *)
hc_run no_tbl_ok. hc_keep.
hc_leaf no_tbl_ok.
Qed.
End c.

Print Assumptions hd_check_no_overrun_A.

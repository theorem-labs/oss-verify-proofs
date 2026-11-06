(* check_keys 0x843a4 of fuzz_headamp.asan-ubsan (image B; unstripped sha256
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff; the pinned 53edda9bdeeb has the same loaded
   bytes except .note.gnu.build-id), the image-B walk against lib/A/HPgCSpec.v's hd_check_keys_specX on lib/AU/Img0U.v rsegs. Proves function
   check_keys (written new as the twin of lib/A/HPgChk_check_keys.v; the plumbing is lib/A/HPgChkBase.v and
   lib/AU/HPgChkBaseU.v).
   THE CODE (37 words from 0x843a4; fuzz_headamp.c:261-271): image A's 32 words (lib/A/HPgChk_check_keys.v) at new
   addresses with the .got word 0x9c7f0, and the UBSan alignment check of both pointers first: 0x843ac
   `or a2,a0,a1; andi a2,a2,3; bnez a2,0x84404` (0x84404 `unimp`, the trap), and the `unimp` after the abort call.
   THE TRAP: the engine does not decide the `or`, so the walk splits the `bnez`; the taken side needs
   (res | x) & 3 <> 0 and is refuted by the contract's res mod 4 = 0 and x mod 4 = 0 (HPgChkBase.hc_or_align4).
   The rest is image A's: the words at res + 4 and x + 0x80 are two regions holding the atom w = v mod 2^32, the
   `bne` at 0x843f4 is decided not taken, the shadow entries cover both instrumented checks, `ret` 0x84400; the abort path
   0x8442c is never stepped. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgChkBaseU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgChkBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_CHECK_KEYS : Z := 0x843a4.
(* the 37 words of image B from 0x843a4 *)
Definition kyu_tbl : ctable := build_table rsegs B_CHECK_KEYS 37 TEmpty.
Lemma kyu_tbl_ok : table_ok rsegs kyu_tbl.
Proof. apply build_table_ok0. unfold B_CHECK_KEYS. lia. Qed.

(* the word at res + 4 (env slot 10) and the word at x + 0x80 (env slot 11), both the atom of slot 33 *)
Definition kyu_rs2 : smem :=
[hc_data 10 4 8 [YP09.mkChunk 4 (CVal 4 (SOff 33 0))]; hc_data 11 128 132 [YP09.mkChunk 128 (CVal 4 (SOff 33 0))]].
Definition kyu_fs2 : list (nat * afact) := [hc_pfact 10 2; hc_pfact 11 2; (33%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition kyu_SH2 : list shent := [mkSHE 10 4 8; mkSHE 11 128 132].
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HCU_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HCU_SH_CELL.

Theorem hd_check_keys_B : hd_check_keys_specX rsegs B MT B_CHECK_KEYS.
Proof using MTL HBgot HBcell.
unfold hd_check_keys_specX, hd_check_word_specX, hd_pre. unfold X_KEYS_OFF.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r x v
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 Hr4 Hx4 Vr Vx Shr Shx Ofr Ofx
(Appr & Imgr) (Appx & Imgx) Hap.
hcu_prelude.
destruct (hc_app_fact (r + 4) 4 Appr ltac:(lia)) as (Hr0 & Hr1 & Hr2).
destruct (hc_app_fact (x + 128) 4 Appx ltac:(lia)) as (Hx0 & Hx1 & Hx2).
destruct (hcu_app_apart (r + 4) 4 Imgr ltac:(lia)) as [Drg Drc].
destruct (hcu_app_apart (x + 128) 4 Imgx ltac:(lia)) as [Dxg Dxc].
unfold ASAN_CEIL in *.
apply hc_val4_mod in Vr. apply hc_val4_mod in Vx.
assert (Hv : 0 <= v mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
remember (v mod 2 ^ 32) as w eqn:Hw. clear Hw.
assert (E10 : bv_unsigned (ew (Ereg regs (hc_extra [w])) 10) = r)
by (apply (hc_Ereg_ptr regs _ 10 10%bv r eq_refl H10); unfold HC_PHI in *; lia).
assert (E33 : sv_denot (Ereg regs (hc_extra [w])) (SOff 33 0) = Z_to_bv 64 w)
by (apply hc_denot_atom; [exact (hc_E33 regs w []) | lia]).
assert (U33 : bv_unsigned (ew (Ereg regs (hc_extra [w])) 33) = w)
by (rewrite (hc_E33 regs w []); apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew (Ereg regs (hc_extra [w])) 2) = spZ regs)
by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
pose proof (hc_E32 regs [w]) as E32.
assert (E1 : ew (Ereg regs (hc_extra [w])) 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
unfold cfg_at. change (w64 B_CHECK_KEYS) with (Z_to_bv 64 B_CHECK_KEYS).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
assert (E11 : bv_unsigned (ew (Ereg regs (hc_extra [w])) 11) = x)
by (apply (hc_Ereg_ptr regs _ 11 11%bv x eq_refl H11); unfold HC_PHI in *; lia).
assert (HS : st_ok rsegs (Ereg regs (hc_extra [w])) (ss_hcu B_CHECK_KEYS [] kyu_rs2 kyu_fs2)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 B_CHECK_KEYS) memc (seg_rom rsegs)))).
{ apply (hcu_entry B_CHECK_KEYS [] [w] kyu_rs2 kyu_fs2 W regs memc ltac:(unfold B_CHECK_KEYS; lia) (Forall_nil _));
    try assumption.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (hc_data_ok _ _ 10 r 4 8 _ E10); [lia | unfold HC_PHI in *; lia |].
      apply Forall_cons; [|apply Forall_nil]. exact (hc_chunk4 _ _ r 4 (SOff 33 0) w E33 Hv Vr).
    + apply (hc_data_ok _ _ 11 x 128 132 _ E11); [lia | unfold HC_PHI in *; lia |].
      apply Forall_cons; [|apply Forall_nil]. exact (hc_chunk4 _ _ x 128 (SOff 33 0) w E33 Hv Vx).
  - unfold hcu_base_regions, kyu_rs2, hc_stack_region, hcu_got_region, hcu_cell_region, hc_data, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E10, E11.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold HCU_GOT_SH, HCU_SH_CELL in *. repeat split; lia.
  - cbn [atoms_ok kyu_fs2 hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
    unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
assert (SHOK : sh_ok rsegs hc_Bx kyu_SH2 (Ereg regs (hc_extra [w])) (mrestrict (w_H W) memc)).
{ unfold sh_ok, kyu_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (hc_shent (w_H W) memc _ 10 r 4 8); [exact Shr | exact Appr | exact E32 | exact E10 | lia].
  - apply (hc_shent (w_H W) memc _ 11 x 128 132); [exact Shx | exact Appx | exact E32 | exact E11 | lia]. }
remember (Ereg regs (hc_extra [w])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hc_extra [w])) E) by (subst E; apply env_agree_refl).
clear HE. rename Usp into B2.
(* to the alignment trap's bnez (0x843b4) *)
hc_run kyu_tbl_ok. hc_keep.
hc_branch kyu_tbl_ok.
- (* taken: (res | x) & 3 <> 0, the trap; against res mod 4 = 0 and x mod 4 = 0 *)
  exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Ht end.
  rewrite branch_ne_U, (hc_or_align4 E 10 11 r x E10 E11 Hr4 Hx4), (U_lit E 0) in Ht by lia.
  cbn in Ht. discriminate Ht.
- (* not taken: on through the two checked words, stop at the ret *)
  hc_run kyu_tbl_ok. hc_keep.
  hc_leaf kyu_tbl_ok.
Qed.
End c.

Print Assumptions hd_check_keys_B.

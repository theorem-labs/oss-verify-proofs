(* check_refusal 0x84368 of fuzz_headamp.asan (unstripped sha256
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a; the pinned f3e0669d2819 has the same loaded
   bytes except .note.gnu.build-id), the image-A walk against lib/A/HPgCSpec.v's hd_check_refusal_specX = hd_check_word_specX at off = 8,
   xoff = X_RF_OFF = 0x84. Proves function check_refusal (written new; the plumbing is lib/A/HPgChkBase.v; the
   proof has the form of lib/A/HPgChk_check_keys.v, whose code differs only in the two offsets and the .got
   displacement).

   THE CODE (32 words, fuzz_headamp.c:275-285):
     0x84368 addi sp,sp,-0x10; sd ra,8(sp); 0x84370 auipc a2,0x18; ld a2,0(a2) (the .got word 0x9c370);
     ld a2,0(a2) (the shadow-offset cell: 0x7fff8000); 0x8437c addi a0,a0,8 (&res->refusal);
     srli / add / 0x84388 lb a3 / 0x8438c bnez a3 (slow arm 0x843bc: `andi a4,a0,7; addi a4,a4,3; blt a4,a3,back`);
     0x84390 addi a1,a1,0x84 (&x->refusal); srli / add / 0x8439c lb a2; 0x843a0 lw a0,0(a0); 0x843a4 bnez a2 (slow
     arm 0x843cc: `andi a3,a1,7; addi a3,a3,3; blt a3,a2,back`); 0x843a8 lw a1,0(a1); 0x843ac bne a0,a1,0x843e0;
     0x843b0 ld ra,8(sp); addi sp,sp,0x10; 0x843b8 ret; 0x843e0 jal __asan_handle_no_return; jal abort.
   The only store is `sd ra,8(sp)` into the save slot [sp - 16, sp).
   The two words are two read-only regions (the contract states [res + 8, res + 12) and [x + 0x84, x + 0x88)
   apart), each holding the word as the atom w = v mod 2^32 (env slot 33; HPgChkBase.hc_val4_mod).
   res is 12 bytes with shadow 00 04: the check of res + 8 sees 0x04 and passes on its slow arm
   ((res + 8) mod 8 + 3 < 4); the token engine follows that arm to the load like the fast one, since the shadow
   entry [res + 8, res + 12) covers the word.
   WHY THE FAILURE BRANCH IS UNREACHABLE: both `lw` read the same atom, so the `bne` at 0x843ac is not taken and
   the jal at 0x843e0 is never stepped. WHY NO REPORT CALL IS REACHED: the shadow entries cover both checked words
   (the contract's range_addressable and hd_app_rng premises), so the token engine continues at each access on both
   arms of each `bnez`. *)
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

Definition A_CHECK_REFUSAL : Z := 0x84368.
(* the 32 words 0x84368 .. 0x843e4 *)
Definition rf_tbl : ctable := build_table rsegs A_CHECK_REFUSAL 32 TEmpty.
Lemma rf_tbl_ok : table_ok rsegs rf_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_REFUSAL. lia. Qed.

(* the word at res + 8 (env slot 10) and the word at x + 0x84 (env slot 11), both the atom of slot 33 *)
Definition rf_rs2 : smem :=
[hc_data 10 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))]; hc_data 11 132 136 [YP09.mkChunk 132 (CVal 4 (SOff 33 0))]].
Definition rf_fs2 : list (nat * afact) := [hc_pfact 10 2; hc_pfact 11 2; (33%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition rf_SH2 : list shent := [mkSHE 10 8 12; mkSHE 11 132 136].
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HC_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HC_SH_CELL.

Theorem hd_check_refusal_A : hd_check_refusal_specX rsegs B MT A_CHECK_REFUSAL.
Proof using MTL HBgot HBcell.
unfold hd_check_refusal_specX, hd_check_word_specX, hd_pre. unfold X_RF_OFF.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r x v
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 Hr4 Hx4 Vr Vx Shr Shx Ofr Ofx
(Appr & Imgr) (Appx & Imgx) Hap.
hc_prelude.
destruct (hc_app_fact (r + 8) 4 Appr ltac:(lia)) as (Hr0 & Hr1 & Hr2).
destruct (hc_app_fact (x + 132) 4 Appx ltac:(lia)) as (Hx0 & Hx1 & Hx2).
destruct (hc_app_apart (r + 8) 4 Imgr ltac:(lia)) as [Drg Drc].
destruct (hc_app_apart (x + 132) 4 Imgx ltac:(lia)) as [Dxg Dxc].
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
unfold cfg_at. change (w64 A_CHECK_REFUSAL) with (Z_to_bv 64 A_CHECK_REFUSAL).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
assert (E11 : bv_unsigned (ew (Ereg regs (hc_extra [w])) 11) = x)
by (apply (hc_Ereg_ptr regs _ 11 11%bv x eq_refl H11); unfold HC_PHI in *; lia).
assert (HS : st_ok rsegs (Ereg regs (hc_extra [w])) (ss_hc A_CHECK_REFUSAL [] rf_rs2 rf_fs2)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_REFUSAL) memc (seg_rom rsegs)))).
{ apply (hc_entry A_CHECK_REFUSAL [] [w] rf_rs2 rf_fs2 W regs memc ltac:(unfold A_CHECK_REFUSAL; lia) (Forall_nil _));
    try assumption.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (hc_data_ok _ _ 10 r 8 12 _ E10); [lia | unfold HC_PHI in *; lia |].
      apply Forall_cons; [|apply Forall_nil]. exact (hc_chunk4 _ _ r 8 (SOff 33 0) w E33 Hv Vr).
    + apply (hc_data_ok _ _ 11 x 132 136 _ E11); [lia | unfold HC_PHI in *; lia |].
      apply Forall_cons; [|apply Forall_nil]. exact (hc_chunk4 _ _ x 132 (SOff 33 0) w E33 Hv Vx).
  - unfold hc_base_regions, rf_rs2, hc_stack_region, hc_got_region, hc_cell_region, hc_data, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E10, E11.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold HC_GOT_SH, HC_SH_CELL in *. repeat split; lia.
  - cbn [atoms_ok rf_fs2 hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
    unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
assert (SHOK : sh_ok rsegs hc_Bx rf_SH2 (Ereg regs (hc_extra [w])) (mrestrict (w_H W) memc)).
{ unfold sh_ok, rf_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (hc_shent (w_H W) memc _ 10 r 8 12); [exact Shr | exact Appr | exact E32 | exact E10 | lia].
  - apply (hc_shent (w_H W) memc _ 11 x 132 136); [exact Shx | exact Appx | exact E32 | exact E11 | lia]. }
remember (Ereg regs (hc_extra [w])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hc_extra [w])) E) by (subst E; apply env_agree_refl).
clear HE. rename Usp into B2.
hc_run rf_tbl_ok. hc_keep.
hc_leaf rf_tbl_ok.
Qed.
End c.

Print Assumptions hd_check_refusal_A.

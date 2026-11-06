(* check_count 0x83f2c of fuzz_headamp.asan-ubsan (image B; unstripped sha256
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff; the pinned 53edda9bdeeb has the same loaded
   bytes except .note.gnu.build-id), the image-B walk against lib/A/HPgCSpec.v's hd_check_count_specX on lib/AU/Img0U.v rsegs. Proves function
   check_count (written new as the twin of lib/A/HPgChk_check_count.v; the plumbing is lib/A/HPgChkBase.v and
   lib/AU/HPgChkBaseU.v).
   THE CODE (40 words, 0x83f2c .. 0x83fc8; fuzz_headamp.c:194-205): image A's 37 words (lib/A/HPgChk_check_count.v)
   at new addresses with the .got word 0x9c7f0, and the UBSan alignment check of res on the rc >= 0 path:
   0x83f44 `andi a1,a2,3; bnez a1,0x83fa0` (0x83fa0 `unimp`, the trap). The engine decides it: res's atom has the
   fact res mod 4 = 0 (the contract's r mod 4 = 0), so the `andi` is 0 and the `bnez` is not taken. The splits are
   A's: 0x83f3c `blt a1,a0` (cap < rc) and 0x83f88 `blt a1,a0` (keys < rc); `ret` 0x83f94; the abort path
   0x83f98. The two instrumented checks at 0x83f60 / 0x83f7c (slow arms 0x83fa4 / 0x83fb8) are covered by the
   shadow entry [res, res + 8). WHY THE FAILURE BRANCH AND THE TRAP ARE UNREACHABLE: as on image A, plus the
   decided alignment test. *)
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

Definition B_CHECK_COUNT : Z := 0x83f2c.
(* the 40 words of image B from 0x83f2c *)
Definition cu_tbl : ctable := build_table rsegs B_CHECK_COUNT 40 TEmpty.
Lemma cu_tbl_ok : table_ok rsegs cu_tbl.
Proof. apply build_table_ok0. unfold B_CHECK_COUNT. lia. Qed.

(* rc = -1: a0 the literal -1, no data region *)
Definition cu_ov0 : list (bv 5 * sv) := [((10%bv : bv 5), SLit (-1))].
(* rc >= 0: the 8 bytes at res (env slot 12): res->n = a0's atom, res->keys = slot 33's atom *)
Definition cu_rs : smem := [hc_data 12 0 8 [YP09.mkChunk 0 (CVal 4 (SOff 10 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0))]].
Definition cu_fs : list (nat * afact) :=
[(10%nat, mkAF 0 (2 ^ 31 - 1) 0); (11%nat, mkAF 0 (2 ^ 31 - 1) 0); hc_pfact 12 2; (33%nat, mkAF 0 (2 ^ 31 - 1) 0)].
Definition cu_SH : list shent := [mkSHE 12 0 8].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = HCU_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = HCU_SH_CELL.

Theorem hd_check_count_B : hd_check_count_specX rsegs B MT B_CHECK_COUNT.
Proof using MTL HBgot HBcell.
unfold hd_check_count_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc cap keys r
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 H12 Hrc Hcap Hpos.
hcu_prelude.
unfold cfg_at. change (w64 B_CHECK_COUNT) with (Z_to_bv 64 B_CHECK_COUNT).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
destruct (Z.eq_dec rcc (-1)) as [Hm1 | Hn1].
- (* rc = -1 *)
  subst rcc. clear Hpos.
  assert (Usp : bv_unsigned (ew (Ereg regs (hc_extra [])) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  pose proof (hc_E32 regs []) as E32.
  assert (E1 : ew (Ereg regs (hc_extra [])) 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
  assert (E11 : ew (Ereg regs (hc_extra [])) 11 = Z_to_bv 64 cap) by exact (hc_ew regs _ 11 11%bv cap eq_refl H11).
  assert (HS : st_ok rsegs (Ereg regs (hc_extra [])) (ss_hcu B_CHECK_COUNT cu_ov0 [] [])
    (restrict (w_H W) (mkst regs (Z_to_bv 64 B_CHECK_COUNT) memc (seg_rom rsegs)))).
  { apply (hcu_entry B_CHECK_COUNT cu_ov0 [] [] [] W regs memc ltac:(unfold B_CHECK_COUNT; lia)); try assumption.
    - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [apply hc_nz; vm_compute; discriminate|].
      rewrite hc_lit. symmetry. exact H10.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - unfold hcu_base_regions, hc_stack_region, hcu_got_region, hcu_cell_region, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold HCU_GOT_SH, HCU_SH_CELL in *. repeat split; lia.
    - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold hc_SB, SHADOW_OFF in *. repeat split; lia. }
  assert (SHOK : sh_ok rsegs hc_Bx [] (Ereg regs (hc_extra [])) (mrestrict (w_H W) memc)) by constructor.
  remember (Ereg regs (hc_extra [])) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hc_extra [])) E) by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  (* 0x83f2c .. 0x83f38 (not taken), stop at 0x83f3c blt a1,a0 *)
  hc_run cu_tbl_ok. hc_keep.
  hc_branch cu_tbl_ok.
  + (* taken: cap < -1, against -1 <= cap *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Ht end.
    cbn [branch_taken sv_denot ew ewset Nat.eqb Nat.ltb Nat.leb] in Ht.
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E11 in Ht. rewrite hc_lts in Ht by lia. apply Z.ltb_lt in Ht. lia.
  + (* not taken: 0x83f40 bltz taken; stop at 0x83f94 ret *)
    hc_run cu_tbl_ok. hc_keep.
    hc_leaf cu_tbl_ok.
- (* rc >= 0 *)
  assert (Hr0 : 0 <= rcc) by lia.
  destruct (Hpos Hr0) as (Hr4 & Vn & Vk & Hkeys & Shr & Ofr & Appr & Imgr). clear Hpos.
  destruct (hc_app_fact r 8 Appr ltac:(lia)) as (Hp0 & Hp1 & Hp2).
  destruct (hcu_app_apart r 8 Imgr ltac:(lia)) as [Drg Drc].
  unfold ASAN_CEIL in *.
  rewrite (Z.mod_small rcc) in Vn by lia. rewrite (Z.mod_small keys) in Vk by lia.
  assert (Usp : bv_unsigned (ew (Ereg regs (hc_extra [keys])) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  pose proof (hc_E32 regs [keys]) as E32.
  assert (E1 : ew (Ereg regs (hc_extra [keys])) 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
  assert (E10 : ew (Ereg regs (hc_extra [keys])) 10 = Z_to_bv 64 rcc) by exact (hc_ew regs _ 10 10%bv rcc eq_refl H10).
  assert (E11 : ew (Ereg regs (hc_extra [keys])) 11 = Z_to_bv 64 cap) by exact (hc_ew regs _ 11 11%bv cap eq_refl H11).
  pose proof (hc_E33 regs keys []) as E33.
  assert (U10 : bv_unsigned (ew (Ereg regs (hc_extra [keys])) 10) = rcc) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew (Ereg regs (hc_extra [keys])) 11) = cap) by (rewrite E11; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew (Ereg regs (hc_extra [keys])) 12) = r)
  by (apply (hc_Ereg_ptr regs _ 12 12%bv r eq_refl H12); unfold HC_PHI in *; lia).
  assert (U33 : bv_unsigned (ew (Ereg regs (hc_extra [keys])) 33) = keys) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs (Ereg regs (hc_extra [keys])) (ss_hcu B_CHECK_COUNT [] cu_rs cu_fs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 B_CHECK_COUNT) memc (seg_rom rsegs)))).
  { apply (hcu_entry B_CHECK_COUNT [] [keys] cu_rs cu_fs W regs memc ltac:(unfold B_CHECK_COUNT; lia) (Forall_nil _));
      try assumption.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      apply (hc_data_ok _ _ 12 r 0 8 _ U12); [lia | unfold HC_PHI in *; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (hc_chunk4 _ _ r 0 (SOff 10 0) rcc); [apply hc_denot_atom; [exact E10 | lia] | lia |].
        rewrite Z.add_0_r. exact Vn.
      + apply (hc_chunk4 _ _ r 4 (SOff 33 0) keys); [apply hc_denot_atom; [exact E33 | lia] | lia | exact Vk].
    - unfold hcu_base_regions, cu_rs, hc_stack_region, hcu_got_region, hcu_cell_region, hc_data, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U12.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold HCU_GOT_SH, HCU_SH_CELL in *. repeat split; lia.
    - cbn [atoms_ok cu_fs hc_pfact]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, U11, U12, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold hc_SB, SHADOW_OFF, HC_PHI in *. repeat split; lia. }
  assert (SHOK : sh_ok rsegs hc_Bx cu_SH (Ereg regs (hc_extra [keys])) (mrestrict (w_H W) memc)).
  { unfold sh_ok, cu_SH. apply Forall_cons; [|apply Forall_nil].
    apply (hc_shent (w_H W) memc _ 12 r 0 8); [rewrite Z.add_0_r; exact Shr | rewrite Z.add_0_r; exact Appr | exact E32 | exact U12 | lia]. }
  remember (Ereg regs (hc_extra [keys])) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hc_extra [keys])) E) by (subst E; apply env_agree_refl).
  clear HE. rename Usp into B2.
  (* 0x83f2c .. 0x83f38 (not taken: rc >= 0), stop at 0x83f3c blt a1,a0 *)
  hc_run cu_tbl_ok. hc_keep.
  hc_branch cu_tbl_ok.
  + (* taken: cap < rc, against rc <= cap *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Ht end.
    cbn [branch_taken sv_denot ew ewset Nat.eqb Nat.ltb Nat.leb] in Ht.
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E10, E11 in Ht. rewrite hc_lts in Ht by lia. apply Z.ltb_lt in Ht. lia.
  + (* not taken: the alignment test 0x83f48 (decided), the two checked words; stop at 0x83f88 blt a1,a0 *)
    hc_run cu_tbl_ok. hc_keep.
    hc_branch cu_tbl_ok.
    * (* taken: keys < rc, against rc <= keys *)
      exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Ht end.
      cbn [branch_taken sv_denot ew ewset Nat.eqb Nat.ltb Nat.leb] in Ht.
      rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E10, E33 in Ht. rewrite hc_lts in Ht by lia. apply Z.ltb_lt in Ht. lia.
    * (* not taken: stop at 0x83f94 ret *)
      hc_run cu_tbl_ok. hc_keep.
      hc_leaf cu_tbl_ok.
Qed.
End c.

Print Assumptions hd_check_count_B.

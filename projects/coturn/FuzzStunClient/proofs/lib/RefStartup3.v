(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefImg RefStartupDefs Ref_code_1b598_1b848 Ref_code_24180_2418c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac ckpt rr Hrr :=
  lazymatch goal with |- context [mkst ?ch ?pc ?m ?ro] => remember ch as rr eqn:Hrr end.
Ltac ckv Hrr := rewrite Hrr; gres; pin; first [reflexivity | bveq].

Section P4.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Abbreviation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Ltac uJ := unfold J_aux, aux_base.
  Ltac uD := unfold D_libc.
  Ltac rdJ := rewrite rdn_cmem_win by region_side; uJ; rd_hit8.
  Ltac rdD L := rewrite rdn_cmem_data by region_side; uD; peel; exact L.
  Ltac rdDh := rewrite rdn_cmem_data by region_side; uD; rd_hit8.

  Lemma p4_run : forall G, bwd SEGS G -> forall regs Jf rom (s1v : word),
    wfJ sp0 Jf ->
    getr regs 1 = Z_to_bv 64 0x1b388 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 0x10800 ->
    getr regs 8 = pn_w sp0 av ev ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 0x56a38 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 0x10800 ->
        getr regs' 4 = Z_to_bv 64 0x367b0 ->
        getr regs' 10 = Z_to_bv 64 0x567b8 ->
        getr regs' 11 = Z_to_bv 64 0x56a70 ->
        getr regs' 17 = Z_to_bv 64 96 ->
        getr regs' 18 = Z_to_bv 64 0x366e8 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        G (mkst regs' (0x1b7f4 : word)
             (CM (J_tls sp0 (J_aux sp0 av ev uid hw Jf) (Z_to_bv 64 0x1b388) (pn_w sp0 av ev) s1v
                        (Z_to_bv 64 0x56a38) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))
                 (D_tlsA (D_libc sp0 av ev hw))) rom)) ->
    G (mkst regs (0x1b598 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs Jf rom s1v HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof (u64_range sp0) as Hsp.
    eapply HG.
    {
      sv F_1b598 D_1b598 (Z_to_bv 64 (bv_unsigned sp0 - 480)).   (* [comment removed for export] *)
      stw F_1b59c D_1b59c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 0x1b388) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b5a0 D_1b5a0 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b5a4 D_1b5a4 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b5a8 D_1b5a8 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 0x56a38) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b5ac D_1b5ac (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b5b0 D_1b5b0 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b5b4 D_1b5b4 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      ld_step F_1b5b8 D_1b5b8 (word_to_le_bytes 8 (Z_to_bv 64 0xa)) (Z_to_bv 64 0xa)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b5bc D_1b5bc.   (* [comment removed for export] *)
      sn F_1b5c0 D_1b5c0.   (* [comment removed for export] *)
      sn F_1b5c4 D_1b5c4.   (* [comment removed for export] *)
      sn F_1b5c8 D_1b5c8.   (* [comment removed for export] *)
      stepb_ft F_1b5cc D_1b5cc ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b5d0 D_1b5d0.   (* [comment removed for export] *)
      sn F_1b5d4 D_1b5d4.   (* [comment removed for export] *)
      sn F_1b5d8 D_1b5d8.   (* [comment removed for export] *)
      ld_step F_1b5dc D_1b5dc (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b5e0 D_1b5e0 (word_to_le_bytes 8 (Z_to_bv 64 0x38)) (Z_to_bv 64 0x38)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b5e4 D_1b5e4.   (* [comment removed for export] *)
      sn F_1b5e8 D_1b5e8.   (* [comment removed for export] *)
      ld_step F_1b5ec D_1b5ec (word_to_le_bytes 4 (Z_to_bv 64 0x20000)) (Z_to_bv 64 0x20000)
        ltac:(rdD img_26638_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b5f0 D_1b5f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_252a8_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b5f4 D_1b5f4.   (* [comment removed for export] *)
      sn F_1b5f8 D_1b5f8.   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr1 Hrr1.
    assert (R2_1 : getr rr1 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr1).
    assert (R3_1 : getr rr1 3 = Z_to_bv 64 0x10800) by (ckv Hrr1).
    assert (R5_1 : getr rr1 5 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R7_1 : getr rr1 7 = Z_to_bv 64 7) by (ckv Hrr1).
    assert (R9_1 : getr rr1 9 = Z_to_bv 64 0x56a38) by (ckv Hrr1).
    assert (R10_1 : getr rr1 10 = Z_to_bv 64 0x38) by (ckv Hrr1).
    assert (R11_1 : getr rr1 11 = Z_to_bv 64 0x567b8) by (ckv Hrr1).
    assert (R13_1 : getr rr1 13 = Z_to_bv 64 0xa) by (ckv Hrr1).
    assert (R15_1 : getr rr1 15 = Z_to_bv 64 0x10040) by (ckv Hrr1).
    assert (R16_1 : getr rr1 16 = Z_to_bv 64 6) by (ckv Hrr1).
    assert (R17_1 : getr rr1 17 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R22_1 : getr rr1 22 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R23_1 : getr rr1 23 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R24_1 : getr rr1 24 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R25_1 : getr rr1 25 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R26_1 : getr rr1 26 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R27_1 : getr rr1 27 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R30_1 : getr rr1 30 = Z_to_bv 64 0x20000) by (ckv Hrr1).
    clear Hrr1.
    eapply HG.
    {
      sn F_1b5fc D_1b5fc.   (* [comment removed for export] *)
      sn F_1b600 D_1b600.   (* [comment removed for export] *)
      sn F_1b604 D_1b604.   (* [comment removed for export] *)
      sn F_1b608 D_1b608.   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6)
        ltac:(rdD img_10040_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_tk F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b60c D_1b60c (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040)
        ltac:(rdD img_10050_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b610 D_1b610.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(rdD img_10078_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(rdD img_100b0_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr2 Hrr2.
    assert (R2_2 : getr rr2 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr2).
    assert (R3_2 : getr rr2 3 = Z_to_bv 64 0x10800) by (ckv Hrr2).
    assert (R5_2 : getr rr2 5 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R7_2 : getr rr2 7 = Z_to_bv 64 7) by (ckv Hrr2).
    assert (R8_2 : getr rr2 8 = Z_to_bv 64 1) by (ckv Hrr2).
    assert (R9_2 : getr rr2 9 = Z_to_bv 64 0x56a38) by (ckv Hrr2).
    assert (R10_2 : getr rr2 10 = Z_to_bv 64 0x38) by (ckv Hrr2).
    assert (R11_2 : getr rr2 11 = Z_to_bv 64 0x567b8) by (ckv Hrr2).
    assert (R13_2 : getr rr2 13 = Z_to_bv 64 8) by (ckv Hrr2).
    assert (R16_2 : getr rr2 16 = Z_to_bv 64 6) by (ckv Hrr2).
    assert (R17_2 : getr rr2 17 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R22_2 : getr rr2 22 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R23_2 : getr rr2 23 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R24_2 : getr rr2 24 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R25_2 : getr rr2 25 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R26_2 : getr rr2 26 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R27_2 : getr rr2 27 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R28_2 : getr rr2 28 = Z_to_bv 64 0x6474e551) by (ckv Hrr2).
    assert (R29_2 : getr rr2 29 = Z_to_bv 64 0x100b0) by (ckv Hrr2).
    assert (R30_2 : getr rr2 30 = Z_to_bv 64 0x20000) by (ckv Hrr2).
    clear Hrr2 R3_1 R2_1 R5_1 R7_1 R9_1 R10_1 R11_1 R13_1 R15_1 R16_1 R17_1 R22_1 R23_1 R24_1 R25_1 R26_1 R27_1 R30_1.
    eapply HG.
    {
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(rdD img_100e8_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(rdD img_10120_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr3 Hrr3.
    assert (R2_3 : getr rr3 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr3).
    assert (R3_3 : getr rr3 3 = Z_to_bv 64 0x10800) by (ckv Hrr3).
    assert (R5_3 : getr rr3 5 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R7_3 : getr rr3 7 = Z_to_bv 64 7) by (ckv Hrr3).
    assert (R8_3 : getr rr3 8 = Z_to_bv 64 1) by (ckv Hrr3).
    assert (R9_3 : getr rr3 9 = Z_to_bv 64 0x56a38) by (ckv Hrr3).
    assert (R10_3 : getr rr3 10 = Z_to_bv 64 0x38) by (ckv Hrr3).
    assert (R11_3 : getr rr3 11 = Z_to_bv 64 0x567b8) by (ckv Hrr3).
    assert (R13_3 : getr rr3 13 = Z_to_bv 64 6) by (ckv Hrr3).
    assert (R16_3 : getr rr3 16 = Z_to_bv 64 6) by (ckv Hrr3).
    assert (R17_3 : getr rr3 17 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R22_3 : getr rr3 22 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R23_3 : getr rr3 23 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R24_3 : getr rr3 24 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R25_3 : getr rr3 25 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R26_3 : getr rr3 26 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R27_3 : getr rr3 27 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R28_3 : getr rr3 28 = Z_to_bv 64 0x6474e551) by (ckv Hrr3).
    assert (R29_3 : getr rr3 29 = Z_to_bv 64 0x10120) by (ckv Hrr3).
    assert (R30_3 : getr rr3 30 = Z_to_bv 64 0x20000) by (ckv Hrr3).
    clear Hrr3 R3_2 R2_2 R5_2 R7_2 R8_2 R9_2 R10_2 R11_2 R13_2 R16_2 R17_2 R22_2 R23_2 R24_2 R25_2 R26_2 R27_2 R28_2 R29_2 R30_2.
    eapply HG.
    {
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 0x6474e552)) (Z_to_bv 64 0x6474e552)
        ltac:(rdD img_10158_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 0x6474e550)) (Z_to_bv 64 0x6474e550)
        ltac:(rdD img_10190_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr4 Hrr4.
    assert (R2_4 : getr rr4 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr4).
    assert (R3_4 : getr rr4 3 = Z_to_bv 64 0x10800) by (ckv Hrr4).
    assert (R5_4 : getr rr4 5 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R7_4 : getr rr4 7 = Z_to_bv 64 7) by (ckv Hrr4).
    assert (R8_4 : getr rr4 8 = Z_to_bv 64 0x6474e550) by (ckv Hrr4).
    assert (R9_4 : getr rr4 9 = Z_to_bv 64 0x56a38) by (ckv Hrr4).
    assert (R10_4 : getr rr4 10 = Z_to_bv 64 0x38) by (ckv Hrr4).
    assert (R11_4 : getr rr4 11 = Z_to_bv 64 0x567b8) by (ckv Hrr4).
    assert (R13_4 : getr rr4 13 = Z_to_bv 64 4) by (ckv Hrr4).
    assert (R16_4 : getr rr4 16 = Z_to_bv 64 6) by (ckv Hrr4).
    assert (R17_4 : getr rr4 17 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R22_4 : getr rr4 22 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R23_4 : getr rr4 23 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R24_4 : getr rr4 24 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R25_4 : getr rr4 25 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R26_4 : getr rr4 26 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R27_4 : getr rr4 27 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R28_4 : getr rr4 28 = Z_to_bv 64 0x6474e551) by (ckv Hrr4).
    assert (R29_4 : getr rr4 29 = Z_to_bv 64 0x10190) by (ckv Hrr4).
    assert (R30_4 : getr rr4 30 = Z_to_bv 64 0x20000) by (ckv Hrr4).
    clear Hrr4 R3_3 R2_3 R5_3 R7_3 R8_3 R9_3 R10_3 R11_3 R13_3 R16_3 R17_3 R22_3 R23_3 R24_3 R25_3 R26_3 R27_3 R28_3 R29_3 R30_3.
    eapply HG.
    {
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 0x6474e551)) (Z_to_bv 64 0x6474e551)
        ltac:(rdD img_101c8_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_ft F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b64c D_1b64c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_101f0_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_tk F_1b650 D_1b650 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4)
        ltac:(rdD img_10200_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr5 Hrr5.
    assert (R2_5 : getr rr5 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr5).
    assert (R3_5 : getr rr5 3 = Z_to_bv 64 0x10800) by (ckv Hrr5).
    assert (R5_5 : getr rr5 5 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R7_5 : getr rr5 7 = Z_to_bv 64 7) by (ckv Hrr5).
    assert (R8_5 : getr rr5 8 = Z_to_bv 64 4) by (ckv Hrr5).
    assert (R9_5 : getr rr5 9 = Z_to_bv 64 0x56a38) by (ckv Hrr5).
    assert (R10_5 : getr rr5 10 = Z_to_bv 64 0x38) by (ckv Hrr5).
    assert (R11_5 : getr rr5 11 = Z_to_bv 64 0x567b8) by (ckv Hrr5).
    assert (R13_5 : getr rr5 13 = Z_to_bv 64 2) by (ckv Hrr5).
    assert (R16_5 : getr rr5 16 = Z_to_bv 64 6) by (ckv Hrr5).
    assert (R17_5 : getr rr5 17 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R22_5 : getr rr5 22 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R23_5 : getr rr5 23 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R24_5 : getr rr5 24 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R25_5 : getr rr5 25 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R26_5 : getr rr5 26 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R27_5 : getr rr5 27 = Z_to_bv 64 0) by (ckv Hrr5).
    assert (R28_5 : getr rr5 28 = Z_to_bv 64 0x6474e551) by (ckv Hrr5).
    assert (R29_5 : getr rr5 29 = Z_to_bv 64 0x10200) by (ckv Hrr5).
    clear Hrr5 R3_4 R2_4 R5_4 R7_4 R8_4 R9_4 R10_4 R11_4 R13_4 R16_4 R17_4 R22_4 R23_4 R24_4 R25_4 R26_4 R27_4 R28_4 R29_4 R30_4.
    eapply HG.
    {
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_ft F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b620 D_1b620 (word_to_le_bytes 4 (Z_to_bv 64 0x70000003)) (Z_to_bv 64 0x70000003)
        ltac:(rdD img_10238_4) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b624 D_1b624 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b628 D_1b628 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b63c D_1b63c.   (* [comment removed for export] *)
      stepb_ft F_1b640 D_1b640 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b644 D_1b644.   (* [comment removed for export] *)
      stepb_tk F_1b648 D_1b648 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b668 D_1b668.   (* [comment removed for export] *)
      sn F_1b66c D_1b66c.   (* [comment removed for export] *)
      sn F_1b614 D_1b614.   (* [comment removed for export] *)
      sn F_1b618 D_1b618.   (* [comment removed for export] *)
      stepb_tk F_1b61c D_1b61c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_tk F_1b670 D_1b670 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b6a8 D_1b6a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_567c8_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b6ac D_1b6ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_567d8_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b6b0 D_1b6b0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_567e0_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr6 Hrr6.
    assert (R2_6 : getr rr6 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr6).
    assert (R3_6 : getr rr6 3 = Z_to_bv 64 0x10800) by (ckv Hrr6).
    assert (R9_6 : getr rr6 9 = Z_to_bv 64 0x56a38) by (ckv Hrr6).
    assert (R10_6 : getr rr6 10 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R11_6 : getr rr6 11 = Z_to_bv 64 0x567b8) by (ckv Hrr6).
    assert (R12_6 : getr rr6 12 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R13_6 : getr rr6 13 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R16_6 : getr rr6 16 = Z_to_bv 64 6) by (ckv Hrr6).
    assert (R22_6 : getr rr6 22 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R23_6 : getr rr6 23 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R24_6 : getr rr6 24 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R25_6 : getr rr6 25 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R26_6 : getr rr6 26 = Z_to_bv 64 0) by (ckv Hrr6).
    assert (R27_6 : getr rr6 27 = Z_to_bv 64 0) by (ckv Hrr6).
    clear Hrr6 R3_5 R2_5 R5_5 R7_5 R8_5 R9_5 R10_5 R11_5 R13_5 R16_5 R17_5 R22_5 R23_5 R24_5 R25_5 R26_5 R27_5 R28_5 R29_5.
    eapply HG.
    {
      sn F_1b6b4 D_1b6b4.   (* [comment removed for export] *)
      sn F_1b6b8 D_1b6b8.   (* [comment removed for export] *)
      sn F_1b6bc D_1b6bc.   (* [comment removed for export] *)
      sn F_1b6c0 D_1b6c0.   (* [comment removed for export] *)
      sn F_1b6c4 D_1b6c4.   (* [comment removed for export] *)
      sn F_1b6c8 D_1b6c8.   (* [comment removed for export] *)
      sn F_1b6cc D_1b6cc.   (* [comment removed for export] *)
      stw F_1b6d0 D_1b6d0 (Z_to_bv 64 0x567d8) (Z_to_bv 64 0) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b6d4 D_1b6d4 (Z_to_bv 64 0x567e8) (Z_to_bv 64 0) ltac:(ok_data).   (* [comment removed for export] *)
      stepb_ft F_1b6d8 D_1b6d8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b6dc D_1b6dc.   (* [comment removed for export] *)
      stw F_1b6e0 D_1b6e0 (Z_to_bv 64 0x567e0) (Z_to_bv 64 8) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1b6e4 D_1b6e4.   (* [comment removed for export] *)
      sn F_1b6e8 D_1b6e8.   (* [comment removed for export] *)
      sn F_1b6ec D_1b6ec.   (* [comment removed for export] *)
      sn F_1b6f0 D_1b6f0.   (* [comment removed for export] *)
      sn F_1b6f4 D_1b6f4.   (* [comment removed for export] *)
      sn F_1b6f8 D_1b6f8.   (* [comment removed for export] *)
      stw F_1b6fc D_1b6fc (Z_to_bv 64 0x56a50) (Z_to_bv 64 0xe0) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b700 D_1b700 (Z_to_bv 64 0x56a58) (Z_to_bv 64 8) ltac:(ok_data).   (* [comment removed for export] *)
      stepb_tk F_1b704 D_1b704 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b738 D_1b738.   (* [comment removed for export] *)
      ld_step F_1b73c D_1b73c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_56a48_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b740 D_1b740 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_56a60_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b744 D_1b744.   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr7 Hrr7.
    assert (R2_7 : getr rr7 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr7).
    assert (R3_7 : getr rr7 3 = Z_to_bv 64 0x10800) by (ckv Hrr7).
    assert (R9_7 : getr rr7 9 = Z_to_bv 64 0x56a38) by (ckv Hrr7).
    assert (R11_7 : getr rr7 11 = Z_to_bv 64 0xe0) by (ckv Hrr7).
    assert (R12_7 : getr rr7 12 = Z_to_bv 64 0) by (ckv Hrr7).
    assert (R13_7 : getr rr7 13 = Z_to_bv 64 0x36738) by (ckv Hrr7).
    assert (R14_7 : getr rr7 14 = Z_to_bv 64 7) by (ckv Hrr7).
    assert (R16_7 : getr rr7 16 = Z_to_bv 64 6) by (ckv Hrr7).
    assert (R19_7 : getr rr7 19 = Z_to_bv 64 0) by (ckv Hrr7).
    assert (R22_7 : getr rr7 22 = Z_to_bv 64 0) by (ckv Hrr7).
    assert (R23_7 : getr rr7 23 = Z_to_bv 64 0) by (ckv Hrr7).
    assert (R24_7 : getr rr7 24 = Z_to_bv 64 0) by (ckv Hrr7).
    assert (R25_7 : getr rr7 25 = Z_to_bv 64 0) by (ckv Hrr7).
    assert (R26_7 : getr rr7 26 = Z_to_bv 64 0) by (ckv Hrr7).
    assert (R27_7 : getr rr7 27 = Z_to_bv 64 0) by (ckv Hrr7).
    clear Hrr7 R3_6 R2_6 R9_6 R10_6 R11_6 R12_6 R13_6 R16_6 R22_6 R23_6 R24_6 R25_6 R26_6 R27_6.
    eapply HG.
    {
      sn F_1b748 D_1b748.   (* [comment removed for export] *)
      sn F_1b74c D_1b74c.   (* [comment removed for export] *)
      sn F_1b750 D_1b750.   (* [comment removed for export] *)
      sn F_1b754 D_1b754.   (* [comment removed for export] *)
      sn F_1b758 D_1b758.   (* [comment removed for export] *)
      sn F_1b75c D_1b75c.   (* [comment removed for export] *)
      sn F_1b760 D_1b760.   (* [comment removed for export] *)
      sn F_1b764 D_1b764.   (* [comment removed for export] *)
      sn F_1b768 D_1b768.   (* [comment removed for export] *)
      sn F_1b76c D_1b76c.   (* [comment removed for export] *)
      stepb_tk F_1b770 D_1b770 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stw F_1b7b8 D_1b7b8 (Z_to_bv 64 0x367c0) (Z_to_bv 64 0) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b7bc D_1b7bc (Z_to_bv 64 0x367a8) (Z_to_bv 64 0x367c0) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b7c0 D_1b7c0 (Z_to_bv 64 0x366e8) (Z_to_bv 64 0x366e8) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1b7c4 D_1b7c4.   (* [comment removed for export] *)
      sn F_1b7c8 D_1b7c8.   (* [comment removed for export] *)
      sn F_24180 D_24180.   (* [comment removed for export] *)
      sn F_24184 D_24184.   (* [comment removed for export] *)
      stepret F_24188 D_24188 (Z_to_bv 64 0x1b7cc) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_1b7cc D_1b7cc ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepb_ft F_1b7d0 D_1b7d0 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_1b7d4 D_1b7d4.   (* [comment removed for export] *)
      stw F_1b7d8 D_1b7d8 (Z_to_bv 64 0x56a38) (Z_to_bv 64 1) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1b7dc D_1b7dc.   (* [comment removed for export] *)
      sn F_1b7e0 D_1b7e0.   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr8 Hrr8.
    assert (R2_8 : getr rr8 2 = Z_to_bv 64 (bv_unsigned sp0 - 480)) by (ckv Hrr8).
    assert (R3_8 : getr rr8 3 = Z_to_bv 64 0x10800) by (ckv Hrr8).
    assert (R4_8 : getr rr8 4 = Z_to_bv 64 0x367b0) by (ckv Hrr8).
    assert (R9_8 : getr rr8 9 = Z_to_bv 64 0x56a38) by (ckv Hrr8).
    assert (R10_8 : getr rr8 10 = Z_to_bv 64 2) by (ckv Hrr8).
    assert (R11_8 : getr rr8 11 = Z_to_bv 64 0x567e0) by (ckv Hrr8).
    assert (R16_8 : getr rr8 16 = Z_to_bv 64 6) by (ckv Hrr8).
    assert (R18_8 : getr rr8 18 = Z_to_bv 64 0x366e8) by (ckv Hrr8).
    assert (R22_8 : getr rr8 22 = Z_to_bv 64 0) by (ckv Hrr8).
    assert (R23_8 : getr rr8 23 = Z_to_bv 64 0) by (ckv Hrr8).
    assert (R24_8 : getr rr8 24 = Z_to_bv 64 0) by (ckv Hrr8).
    assert (R25_8 : getr rr8 25 = Z_to_bv 64 0) by (ckv Hrr8).
    assert (R26_8 : getr rr8 26 = Z_to_bv 64 0) by (ckv Hrr8).
    assert (R27_8 : getr rr8 27 = Z_to_bv 64 0) by (ckv Hrr8).
    clear Hrr8 R3_7 R2_7 R9_7 R11_7 R12_7 R13_7 R14_7 R16_7 R19_7 R22_7 R23_7 R24_7 R25_7 R26_7 R27_7.
    eapply HG.
    {
      stw F_1b7e4 D_1b7e4 (Z_to_bv 64 0x36710) (Z_to_bv 64 2) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1b7e8 D_1b7e8.   (* [comment removed for export] *)
      sn F_1b7ec D_1b7ec.   (* [comment removed for export] *)
      sn F_1b7f0 D_1b7f0.   (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; gres; pin; first [reflexivity | bveq].
  Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

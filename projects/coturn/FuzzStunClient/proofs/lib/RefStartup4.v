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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefImg RefStartupDefs Ref_code_13894_14104 Ref_code_1b104_1c2fc Ref_code_235f0_2427c.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Ref_code_1b598_1b848.
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

Lemma b2z_small : forall bs : list byte, (length bs <= 8)%nat ->
  bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros bs Hl. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs).
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
  rewrite u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rd_guard3 : forall segs (D : word -> option byte) (X Y : list byte),
  length X = 4%nat -> length Y = 4%nat ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 0x567f0) X) (Z_to_bv 64 0x567f4) Y) (Z_to_bv 64 0x567f1) [Z_to_bv 8 0])
      (Z_to_bv 64 0x567f0) 8
  = Some (nth 0 X (Z_to_bv 8 0) :: Z_to_bv 8 0 :: nth 2 X (Z_to_bv 8 0) :: nth 3 X (Z_to_bv 8 0) :: Y).
Proof.
  intros segs D X Y HX HY.
  destruct X as [|x0 [|x1 [|x2 [|x3 [|]]]]]; try discriminate.
  destruct Y as [|y0 [|y1 [|y2 [|y3 [|]]]]]; try discriminate.
  vm_compute. reflexivity.
Qed.

Section P5.
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
  Local Abbreviation rb := (ed_random rdraw) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rnd_ne0 : c_eq (rnd_w sp0 av ev) (Z_to_bv 64 0) = false.
  Proof.
    pose proof rnd_bounds as (A & _). unfold c_eq, bv_eqb. apply Z.eqb_neq. rewrite (u_Z2bv 0) by lia. lia.
  Qed.

  Lemma rnd_al4 : (bv_unsigned (rnd_w sp0 av ev) mod 4 = 0)%Z.
  Proof.
    pose proof rnd_bounds as (_ & _ & C).
    rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite C. reflexivity.
  Qed.

  Lemma rd_rnd_j : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (rbytes rb))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w, rbytes. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rd_rnd_lo : forall J D, rdn SEGS (CM J D) (rnd_w sp0 av ev) 4 = Some (firstn 4 (rbytes rb)).
  Proof.
    intros J D. pose proof (rd_rnd_j J D 0 4 ltac:(lia)) as H.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H. exact H.
  Qed.

  Lemma rd_rnd_hi : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 4)) 4 = Some (firstn 4 (skipn 4 (rbytes rb))).
  Proof. intros J D. exact (rd_rnd_j J D 4 4 ltac:(lia)). Qed.

  Lemma slli_argc : v_slli (argcN av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Ltac rlen := unfold rbytes; rewrite ?length_firstn, ?length_skipn, length_at_random_bytes; cbn; lia.
  Ltac glen := unfold guard_bytes; cbn [length]; rewrite length_N_to_le_bytes; cbn; lia.
  Ltac uJ := unfold J_tls, J_aux, aux_base, J_lsm.
  Ltac uD := unfold D_tlsA, D_libc.
  Ltac rdJ := rewrite rdn_cmem_win by region_side; uJ; rd_hit8.
  Ltac rdJz := rewrite rdn_cmem_win by region_side; uJ; peel; apply rdn_wbytes_zeros_in;
               cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia.
  Ltac rdD L := rewrite rdn_cmem_data by region_side; uD; peel; exact L.
  Ltac RD_GUARD := rewrite rdn_cmem_data by region_side; apply rd_guard3; apply length_N_to_le_bytes.

  (* [comment removed for export] *)
  Definition J5 (Jb : word -> option byte) (s1v : word) : word -> option byte :=
    let J6 := J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb))
                (Z_to_bv 64 0x1b388) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x56a38)
                (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x1b390)))   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x1b584)))    (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argcN av)))              (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x1b4d4)))    (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x25288)).    (* [comment removed for export] *)

  Lemma p5_run : forall G, bwd SEGS G -> forall regs Jb rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 0x10800 ->
    getr regs 4 = Z_to_bv 64 0x367b0 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 0x56a70 ->
    getr regs 18 = Z_to_bv 64 0x366e8 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x1b594 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 0x10800 ->
        getr regs' 4 = Z_to_bv 64 0x367b0 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = argcN av ->
        getr regs' 10 = argcN av ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 0x139e0 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        G (mkst regs' (0x139e0 : word) (CM (J5 Jb s1v) (D_main sp0 av ev hw rb tid)) rom)) ->
    G (mkst regs (0x1b7f8 : word)
         (CM (J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 0x1b388) (pn_w sp0 av ev) s1v
                    (Z_to_bv 64 0x56a38) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))
             (D_tlsA (D_libc sp0 av ev hw))) rom).
  Proof.
    intros G HG regs Jb rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    pose proof (u64_range sp0) as Hsp. pose proof len_av as Hlen.
    eapply HG.
    {
      sn F_1b7f8 D_1b7f8.   (* [comment removed for export] *)
      stw F_1b7fc D_1b7fc (Z_to_bv 64 0x36708) (tid) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b800 D_1b800 (Z_to_bv 64 0x36780) (Z_to_bv 64 0x56a70) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b804 D_1b804 (Z_to_bv 64 0x36760) (Z_to_bv 64 0x36760) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1b808 D_1b808.   (* [comment removed for export] *)
      ld_step F_1b80c D_1b80c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_36490_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stw F_1b810 D_1b810 (Z_to_bv 64 0x366f0) (Z_to_bv 64 0x366e8) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b814 D_1b814 (Z_to_bv 64 0x366f8) (Z_to_bv 64 0x366e8) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1b818 D_1b818 (Z_to_bv 64 0x36700) (Z_to_bv 64 0) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1b81c D_1b81c.   (* [comment removed for export] *)
      ld_step F_1b824 D_1b824 (word_to_le_bytes 8 (Z_to_bv 64 0x1b388)) (Z_to_bv 64 0x1b388)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b828 D_1b828 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b82c D_1b82c (word_to_le_bytes 8 s1v) s1v
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b830 D_1b830 (word_to_le_bytes 8 (Z_to_bv 64 0x56a38)) (Z_to_bv 64 0x56a38)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b834 D_1b834 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b838 D_1b838 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b83c D_1b83c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b840 D_1b840 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stepret F_1b844 D_1b844 (Z_to_bv 64 0x1b388) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      ld_step F_1b388 D_1b388 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b38c D_1b38c.   (* [comment removed for export] *)
      sv F_1b848 D_1b848 (Z_to_bv 64 (bv_unsigned sp0 - 432)).   (* [comment removed for export] *)
      stw F_1b84c D_1b84c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 0x1b390) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stepb_ft F_1b850 D_1b850 ltac:(pin; gres; exact rnd_ne0).   (* [comment removed for export] *)
      sv F_1b854 D_1b854 (rnd_w sp0 av ev).   (* [comment removed for export] *)
      sn F_1b858 D_1b858.   (* [comment removed for export] *)
      ld_step F_1b85c D_1b85c (word_to_le_bytes 8 (Z_to_bv 64 0x567f0)) (Z_to_bv 64 0x567f0)
        ltac:(rdD img_24ce8_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b860 D_1b860.   (* [comment removed for export] *)
      sn F_1b864 D_1b864.   (* [comment removed for export] *)
      stepiv F_23640 D_23640 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; exact rnd_al4).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr1 Hrr1.
    assert (R1_1 : getr rr1 1 = Z_to_bv 64 0x1b868) by (ckv Hrr1).
    assert (R2_1 : getr rr1 2 = Z_to_bv 64 (bv_unsigned sp0 - 432)) by (ckv Hrr1).
    assert (R3_1 : getr rr1 3 = Z_to_bv 64 0x10800) by (ckv Hrr1).
    assert (R4_1 : getr rr1 4 = Z_to_bv 64 0x367b0) by (ckv Hrr1).
    assert (R10_1 : getr rr1 10 = Z_to_bv 64 0x567f0) by (ckv Hrr1).
    assert (R11_1 : getr rr1 11 = rnd_w sp0 av ev) by (ckv Hrr1).
    assert (R12_1 : getr rr1 12 = Z_to_bv 64 8) by (ckv Hrr1).
    assert (R13_1 : getr rr1 13 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R19_1 : getr rr1 19 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R20_1 : getr rr1 20 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R21_1 : getr rr1 21 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R22_1 : getr rr1 22 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R23_1 : getr rr1 23 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R24_1 : getr rr1 24 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R25_1 : getr rr1 25 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R26_1 : getr rr1 26 = Z_to_bv 64 0) by (ckv Hrr1).
    assert (R27_1 : getr rr1 27 = Z_to_bv 64 0) by (ckv Hrr1).
    clear Hrr1 H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27.
    eapply HG.
    {
      stepb_tk F_23644 D_23644 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23754 D_23754.   (* [comment removed for export] *)
      sn F_23758 D_23758.   (* [comment removed for export] *)
      stepb_ft F_2375c D_2375c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23760 D_23760.   (* [comment removed for export] *)
      stepb_tk F_23764 D_23764 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_2379c D_2379c.   (* [comment removed for export] *)
      stepb_ft F_237a0 D_237a0 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_237a4 D_237a4 (firstn 4 (rbytes rb)) (Z_to_bv 64 (bytes_le_to_Z (firstn 4 (rbytes rb))))
        ltac:(exact (rd_rnd_lo _ _)) ltac:(apply b2z_small; rlen).   (* [comment removed for export] *)
      ld_step F_237a8 D_237a8 (firstn 4 (skipn 4 (rbytes rb))) (Z_to_bv 64 (bytes_le_to_Z (firstn 4 (skipn 4 (rbytes rb)))))
        ltac:(exact (rd_rnd_hi _ _)) ltac:(apply b2z_small; rlen).   (* [comment removed for export] *)
      stw F_237ac D_237ac (Z_to_bv 64 0x567f0) (ssp_lo rb) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_237b0 D_237b0 (Z_to_bv 64 0x567f4) (ssp_hi rb) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_237b4 D_237b4.   (* [comment removed for export] *)
      sv F_237b8 D_237b8 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).   (* [comment removed for export] *)
      sn F_237bc D_237bc.   (* [comment removed for export] *)
      stepb_tk F_237c0 D_237c0 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23a00 D_23a00.   (* [comment removed for export] *)
      stepb_ft F_23a04 D_23a04 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23a08 D_23a08.   (* [comment removed for export] *)
      stepb_ft F_23a0c D_23a0c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepret F_23a10 D_23a10 (Z_to_bv 64 0x1b868) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1b868 D_1b868.   (* [comment removed for export] *)
      sn F_1b884 D_1b884.   (* [comment removed for export] *)
      ld_step F_1b888 D_1b888 (word_to_le_bytes 8 (Z_to_bv 64 0x567f0)) (Z_to_bv 64 0x567f0)
        ltac:(rdD img_24ce8_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stw F_1b88c D_1b88c (Z_to_bv 64 0x567f1) (Z_to_bv 64 0) ltac:(ok_data).   (* [comment removed for export] *)
      ld_step F_1b890 D_1b890 (guard_bytes rb) (canary_w rb)
        ltac:(RD_GUARD) ltac:(unfold canary_w; apply b2z_small; glen).   (* [comment removed for export] *)
      sn F_1b894 D_1b894.   (* [comment removed for export] *)
      stw F_1b898 D_1b898 (Z_to_bv 64 0x367a0) (canary_w rb) ltac:(ok_data).   (* [comment removed for export] *)
      ld_step F_1b89c D_1b89c (word_to_le_bytes 8 (Z_to_bv 64 0x1b390)) (Z_to_bv 64 0x1b390)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b8a0 D_1b8a0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr2 Hrr2.
    assert (R1_2 : getr rr2 1 = Z_to_bv 64 0x1b390) by (ckv Hrr2).
    assert (R2_2 : getr rr2 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)) by (ckv Hrr2).
    assert (R3_2 : getr rr2 3 = Z_to_bv 64 0x10800) by (ckv Hrr2).
    assert (R4_2 : getr rr2 4 = Z_to_bv 64 0x367b0) by (ckv Hrr2).
    assert (R19_2 : getr rr2 19 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R20_2 : getr rr2 20 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R21_2 : getr rr2 21 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R22_2 : getr rr2 22 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R23_2 : getr rr2 23 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R24_2 : getr rr2 24 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R25_2 : getr rr2 25 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R26_2 : getr rr2 26 = Z_to_bv 64 0) by (ckv Hrr2).
    assert (R27_2 : getr rr2 27 = Z_to_bv 64 0) by (ckv Hrr2).
    clear Hrr2 R1_1 R2_1 R3_1 R4_1 R10_1 R11_1 R12_1 R13_1 R19_1 R20_1 R21_1 R22_1 R23_1 R24_1 R25_1 R26_1 R27_1.
    eapply HG.
    {
      stepret F_1b8a4 D_1b8a4 (Z_to_bv 64 0x1b390) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      ld_step F_1b390 D_1b390 (word_to_le_bytes 8 (uid)) (uid)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b394 D_1b394 (word_to_le_bytes 8 (uid)) (uid)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b398 D_1b398 ltac:(pin; apply c_eq_refl).   (* [comment removed for export] *)
      ld_step F_1b39c D_1b39c (zeros 8) (Z_to_bv 64 0)
        ltac:(rdJz) ltac:(reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b3a0 D_1b3a0 (zeros 8) (Z_to_bv 64 0)
        ltac:(rdJz) ltac:(reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b3a4 D_1b3a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b3a8 D_1b3a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_tk F_1b3ac D_1b3ac ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b48c D_1b48c (word_to_le_bytes 8 (Z_to_bv 64 0x1b524)) (Z_to_bv 64 0x1b524)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b490 D_1b490 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8))
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b494 D_1b494 (word_to_le_bytes 8 (argcN av)) (argcN av)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b498 D_1b498 (word_to_le_bytes 8 (Z_to_bv 64 0x139e0)) (Z_to_bv 64 0x139e0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b49c D_1b49c (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stepret F_1b4a0 D_1b4a0 (Z_to_bv 64 0x1b524) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1b524 D_1b524.   (* [comment removed for export] *)
      sn F_1b528 D_1b528.   (* [comment removed for export] *)
      sn F_1b52c D_1b52c.   (* [comment removed for export] *)
      sv F_1b530 D_1b530 (argcN av).   (* [comment removed for export] *)
      sv F_1b534 D_1b534 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      ld_step F_1b538 D_1b538 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b53c D_1b53c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b540 D_1b540 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b544 D_1b544 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b548 D_1b548 (Z_to_bv 64 (bv_unsigned sp0)).   (* [comment removed for export] *)
      stepret F_1b54c D_1b54c (Z_to_bv 64 0x1b550) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sv F_1b550 D_1b550 (Z_to_bv 64 (bv_unsigned sp0 - 48)).   (* [comment removed for export] *)
      stw F_1b554 D_1b554 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b558 D_1b558 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b55c D_1b55c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr3 Hrr3.
    assert (R2_3 : getr rr3 2 = Z_to_bv 64 (bv_unsigned sp0 - 48)) by (ckv Hrr3).
    assert (R3_3 : getr rr3 3 = Z_to_bv 64 0x10800) by (ckv Hrr3).
    assert (R4_3 : getr rr3 4 = Z_to_bv 64 0x367b0) by (ckv Hrr3).
    assert (R10_3 : getr rr3 10 = Z_to_bv 64 0x139e0) by (ckv Hrr3).
    assert (R11_3 : getr rr3 11 = argcN av) by (ckv Hrr3).
    assert (R12_3 : getr rr3 12 = Z_to_bv 64 (bv_unsigned sp0 + 8)) by (ckv Hrr3).
    assert (R18_3 : getr rr3 18 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R19_3 : getr rr3 19 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R20_3 : getr rr3 20 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R21_3 : getr rr3 21 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R22_3 : getr rr3 22 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R23_3 : getr rr3 23 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R24_3 : getr rr3 24 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R25_3 : getr rr3 25 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R26_3 : getr rr3 26 = Z_to_bv 64 0) by (ckv Hrr3).
    assert (R27_3 : getr rr3 27 = Z_to_bv 64 0) by (ckv Hrr3).
    clear Hrr3 R1_2 R2_2 R3_2 R4_2 R19_2 R20_2 R21_2 R22_2 R23_2 R24_2 R25_2 R26_2 R27_2.
    eapply HG.
    {
      stw F_1b560 D_1b560 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b564 D_1b564 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      sv F_1b568 D_1b568 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      sv F_1b56c D_1b56c (argcN av).   (* [comment removed for export] *)
      sn F_1b570 D_1b570.   (* [comment removed for export] *)
      stepiv F_1b574 D_1b574 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; exact slli_argc).   (* [comment removed for export] *)
      sv F_1b578 D_1b578 (Z_to_bv 64 (bv_unsigned sp0 + 8 * Z.of_nat (length av) + 8)).   (* [comment removed for export] *)
      sv F_1b57c D_1b57c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).   (* [comment removed for export] *)
      sn F_1b580 D_1b580.   (* [comment removed for export] *)
      sv F_1b4a4 D_1b4a4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).   (* [comment removed for export] *)
      stw F_1b4a8 D_1b4a8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 0x1b584) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b4ac D_1b4ac (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b4b0 D_1b4b0 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argcN av) ltac:(ok_win HJ).   (* [comment removed for export] *)
      sn F_1b4b4 D_1b4b4.   (* [comment removed for export] *)
      stepret F_1b274 D_1b274 (Z_to_bv 64 0x1b4b8) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1b4b8 D_1b4b8.   (* [comment removed for export] *)
      sn F_1b4bc D_1b4bc.   (* [comment removed for export] *)
      ld_step F_1b4c0 D_1b4c0 (word_to_le_bytes 8 (Z_to_bv 64 0x25288)) (Z_to_bv 64 0x25288)
        ltac:(rdD img_24d08_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b4c4 D_1b4c4 (word_to_le_bytes 8 (Z_to_bv 64 0x25280)) (Z_to_bv 64 0x25280)
        ltac:(rdD img_24d10_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b4c8 D_1b4c8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b4cc D_1b4cc (word_to_le_bytes 8 (Z_to_bv 64 0x138dc)) (Z_to_bv 64 0x138dc)
        ltac:(rdD img_24c80_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepjr F_1b4d0 D_1b4d0 (Z_to_bv 64 0x138dc) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      sv F_138dc D_138dc (Z_to_bv 64 (bv_unsigned sp0 - 96)).   (* [comment removed for export] *)
      stw F_138e0 D_138e0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 0x1b4d4) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_138e4 D_138e4 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 0x25288) ltac:(ok_win HJ).   (* [comment removed for export] *)
      sv F_138e8 D_138e8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).   (* [comment removed for export] *)
      sn F_138ec D_138ec.   (* [comment removed for export] *)
      sn F_138f0 D_138f0.   (* [comment removed for export] *)
      lb_step F_138f4 D_138f4 (Z_to_bv 8 0x0) ltac:(rdD img_26030_1).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_138f8 D_138f8.   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr4 Hrr4.
    assert (R2_4 : getr rr4 2 = Z_to_bv 64 (bv_unsigned sp0 - 96)) by (ckv Hrr4).
    assert (R3_4 : getr rr4 3 = Z_to_bv 64 0x10800) by (ckv Hrr4).
    assert (R4_4 : getr rr4 4 = Z_to_bv 64 0x367b0) by (ckv Hrr4).
    assert (R9_4 : getr rr4 9 = Z_to_bv 64 0x25280) by (ckv Hrr4).
    assert (R10_4 : getr rr4 10 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R18_4 : getr rr4 18 = Z_to_bv 64 0x139e0) by (ckv Hrr4).
    assert (R19_4 : getr rr4 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) by (ckv Hrr4).
    assert (R20_4 : getr rr4 20 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R21_4 : getr rr4 21 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R22_4 : getr rr4 22 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R23_4 : getr rr4 23 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R24_4 : getr rr4 24 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R25_4 : getr rr4 25 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R26_4 : getr rr4 26 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R27_4 : getr rr4 27 = Z_to_bv 64 0) by (ckv Hrr4).
    clear Hrr4 R2_3 R3_3 R4_3 R10_3 R11_3 R12_3 R18_3 R19_3 R20_3 R21_3 R22_3 R23_3 R24_3 R25_3 R26_3 R27_3.
    eapply HG.
    {
      stepb_tk F_138fc D_138fc ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_13908 D_13908.   (* [comment removed for export] *)
      sn F_1390c D_1390c.   (* [comment removed for export] *)
      sn F_13910 D_13910.   (* [comment removed for export] *)
      stw F_13914 D_13914 (Z_to_bv 64 0x26640) (Z_to_bv 64 1) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_13918 D_13918.   (* [comment removed for export] *)
      ld_step F_1391c D_1391c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_24cc0_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_tk F_13920 D_13920 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_13940 D_13940 (word_to_le_bytes 8 (Z_to_bv 64 0x1b4d4)) (Z_to_bv 64 0x1b4d4)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_13944 D_13944 (word_to_le_bytes 8 (Z_to_bv 64 0x25288)) (Z_to_bv 64 0x25288)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_13948 D_13948 (Z_to_bv 64 (bv_unsigned sp0 - 80)).   (* [comment removed for export] *)
      stepret F_1394c D_1394c (Z_to_bv 64 0x1b4d4) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1b4d4 D_1b4d4.   (* [comment removed for export] *)
      stepb_ft F_1b4d8 D_1b4d8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b4dc D_1b4dc (word_to_le_bytes 8 (Z_to_bv 64 0x1b584)) (Z_to_bv 64 0x1b584)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b4e0 D_1b4e0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8))
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b4e4 D_1b4e4 (word_to_le_bytes 8 (argcN av)) (argcN av)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b4e8 D_1b4e8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).   (* [comment removed for export] *)
      stepret F_1b4ec D_1b4ec (Z_to_bv 64 0x1b584) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sv F_1b584 D_1b584 (argcN av).   (* [comment removed for export] *)
      sv F_1b588 D_1b588 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      sv F_1b58c D_1b58c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).   (* [comment removed for export] *)
      stepjr F_1b590 D_1b590 (Z_to_bv 64 0x139e0) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; gres; pin; first [reflexivity | bveq | f_equal; lia].
  Qed.
End P5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbImg UbStartupDefs Ub_code_13974_14104 Ub_code_1b104_1c2fc Ub_code_235f0_245f0  .
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Ub_code_1ba40_1bcf0.
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

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

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
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 0x56ca0) X) (Z_to_bv 64 0x56ca4) Y) (Z_to_bv 64 0x56ca1) [Z_to_bv 8 0])
      (Z_to_bv 64 0x56ca0) 8
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
                (Z_to_bv 64 0x1b830) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x56ee8)
                (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x1b838)))   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x1ba2c)))    (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argcN av)))              (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x1b97c)))    (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x25730)).    (* [comment removed for export] *)

  Lemma p5_run : forall G, bwd SEGS G -> forall regs Jb rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 0x10800 ->
    getr regs 4 = Z_to_bv 64 0x36c60 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 0x56f20 ->
    getr regs 18 = Z_to_bv 64 0x36b98 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x1ba3c ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 0x10800 ->
        getr regs' 4 = Z_to_bv 64 0x36c60 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = argcN av ->
        getr regs' 10 = argcN av ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 0x13ac0 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        G (mkst regs' (0x13ac0 : word) (CM (J5 Jb s1v) (D_main sp0 av ev hw rb tid)) rom)) ->
    G (mkst regs (0x1bca0 : word)
         (CM (J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 0x1b830) (pn_w sp0 av ev) s1v
                    (Z_to_bv 64 0x56ee8) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))
             (D_tlsA (D_libc sp0 av ev hw))) rom).
  Proof.
    intros G HG regs Jb rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    pose proof (u64_range sp0) as Hsp. pose proof len_av as Hlen.
    eapply HG.
    {
      sn F_1bca0 D_1bca0.   (* [comment removed for export] *)
      stw F_1bca4 D_1bca4 (Z_to_bv 64 0x36bb8) (tid) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1bca8 D_1bca8 (Z_to_bv 64 0x36c30) (Z_to_bv 64 0x56f20) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1bcac D_1bcac (Z_to_bv 64 0x36c10) (Z_to_bv 64 0x36c10) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1bcb0 D_1bcb0.   (* [comment removed for export] *)
      ld_step F_1bcb4 D_1bcb4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_36940_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stw F_1bcb8 D_1bcb8 (Z_to_bv 64 0x36ba0) (Z_to_bv 64 0x36b98) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1bcbc D_1bcbc (Z_to_bv 64 0x36ba8) (Z_to_bv 64 0x36b98) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_1bcc0 D_1bcc0 (Z_to_bv 64 0x36bb0) (Z_to_bv 64 0) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1bcc4 D_1bcc4.   (* [comment removed for export] *)
      ld_step F_1bccc D_1bccc (word_to_le_bytes 8 (Z_to_bv 64 0x1b830)) (Z_to_bv 64 0x1b830)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1bcd0 D_1bcd0 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1bcd4 D_1bcd4 (word_to_le_bytes 8 s1v) s1v
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1bcd8 D_1bcd8 (word_to_le_bytes 8 (Z_to_bv 64 0x56ee8)) (Z_to_bv 64 0x56ee8)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1bcdc D_1bcdc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1bce0 D_1bce0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1bce4 D_1bce4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1bce8 D_1bce8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stepret F_1bcec D_1bcec (Z_to_bv 64 0x1b830) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      ld_step F_1b830 D_1b830 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1b834 D_1b834.   (* [comment removed for export] *)
      sv F_1bcf0 D_1bcf0 (Z_to_bv 64 (bv_unsigned sp0 - 432)).   (* [comment removed for export] *)
      stw F_1bcf4 D_1bcf4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 0x1b838) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stepb_ft F_1bcf8 D_1bcf8 ltac:(pin; gres; exact rnd_ne0).   (* [comment removed for export] *)
      sv F_1bcfc D_1bcfc (rnd_w sp0 av ev).   (* [comment removed for export] *)
      sn F_1bd00 D_1bd00.   (* [comment removed for export] *)
      ld_step F_1bd04 D_1bd04 (word_to_le_bytes 8 (Z_to_bv 64 0x56ca0)) (Z_to_bv 64 0x56ca0)
        ltac:(rdD img_25190_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_1bd08 D_1bd08.   (* [comment removed for export] *)
      sn F_1bd0c D_1bd0c.   (* [comment removed for export] *)
      stepiv F_23ae8 D_23ae8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; exact rnd_al4).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr1 Hrr1.
    assert (R1_1 : getr rr1 1 = Z_to_bv 64 0x1bd10) by (ckv Hrr1).
    assert (R2_1 : getr rr1 2 = Z_to_bv 64 (bv_unsigned sp0 - 432)) by (ckv Hrr1).
    assert (R3_1 : getr rr1 3 = Z_to_bv 64 0x10800) by (ckv Hrr1).
    assert (R4_1 : getr rr1 4 = Z_to_bv 64 0x36c60) by (ckv Hrr1).
    assert (R10_1 : getr rr1 10 = Z_to_bv 64 0x56ca0) by (ckv Hrr1).
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
      stepb_tk F_23aec D_23aec ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23bfc D_23bfc.   (* [comment removed for export] *)
      sn F_23c00 D_23c00.   (* [comment removed for export] *)
      stepb_ft F_23c04 D_23c04 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23c08 D_23c08.   (* [comment removed for export] *)
      stepb_tk F_23c0c D_23c0c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23c44 D_23c44.   (* [comment removed for export] *)
      stepb_ft F_23c48 D_23c48 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_23c4c D_23c4c (firstn 4 (rbytes rb)) (Z_to_bv 64 (bytes_le_to_Z (firstn 4 (rbytes rb))))
        ltac:(exact (rd_rnd_lo _ _)) ltac:(apply b2z_small; rlen).   (* [comment removed for export] *)
      ld_step F_23c50 D_23c50 (firstn 4 (skipn 4 (rbytes rb))) (Z_to_bv 64 (bytes_le_to_Z (firstn 4 (skipn 4 (rbytes rb)))))
        ltac:(exact (rd_rnd_hi _ _)) ltac:(apply b2z_small; rlen).   (* [comment removed for export] *)
      stw F_23c54 D_23c54 (Z_to_bv 64 0x56ca0) (ssp_lo rb) ltac:(ok_data).   (* [comment removed for export] *)
      stw F_23c58 D_23c58 (Z_to_bv 64 0x56ca4) (ssp_hi rb) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_23c5c D_23c5c.   (* [comment removed for export] *)
      sv F_23c60 D_23c60 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).   (* [comment removed for export] *)
      sn F_23c64 D_23c64.   (* [comment removed for export] *)
      stepb_tk F_23c68 D_23c68 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23ea8 D_23ea8.   (* [comment removed for export] *)
      stepb_ft F_23eac D_23eac ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_23eb0 D_23eb0.   (* [comment removed for export] *)
      stepb_ft F_23eb4 D_23eb4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      stepret F_23eb8 D_23eb8 (Z_to_bv 64 0x1bd10) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1bd10 D_1bd10.   (* [comment removed for export] *)
      sn F_1bd2c D_1bd2c.   (* [comment removed for export] *)
      ld_step F_1bd30 D_1bd30 (word_to_le_bytes 8 (Z_to_bv 64 0x56ca0)) (Z_to_bv 64 0x56ca0)
        ltac:(rdD img_25190_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stw F_1bd34 D_1bd34 (Z_to_bv 64 0x56ca1) (Z_to_bv 64 0) ltac:(ok_data).   (* [comment removed for export] *)
      ld_step F_1bd38 D_1bd38 (guard_bytes rb) (canary_w rb)
        ltac:(RD_GUARD) ltac:(unfold canary_w; apply b2z_small; glen).   (* [comment removed for export] *)
      sn F_1bd3c D_1bd3c.   (* [comment removed for export] *)
      stw F_1bd40 D_1bd40 (Z_to_bv 64 0x36c50) (canary_w rb) ltac:(ok_data).   (* [comment removed for export] *)
      ld_step F_1bd44 D_1bd44 (word_to_le_bytes 8 (Z_to_bv 64 0x1b838)) (Z_to_bv 64 0x1b838)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1bd48 D_1bd48 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr2 Hrr2.
    assert (R1_2 : getr rr2 1 = Z_to_bv 64 0x1b838) by (ckv Hrr2).
    assert (R2_2 : getr rr2 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)) by (ckv Hrr2).
    assert (R3_2 : getr rr2 3 = Z_to_bv 64 0x10800) by (ckv Hrr2).
    assert (R4_2 : getr rr2 4 = Z_to_bv 64 0x36c60) by (ckv Hrr2).
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
      stepret F_1bd4c D_1bd4c (Z_to_bv 64 0x1b838) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      ld_step F_1b838 D_1b838 (word_to_le_bytes 8 (uid)) (uid)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b83c D_1b83c (word_to_le_bytes 8 (uid)) (uid)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b840 D_1b840 ltac:(pin; apply c_eq_refl).   (* [comment removed for export] *)
      ld_step F_1b844 D_1b844 (zeros 8) (Z_to_bv 64 0)
        ltac:(rdJz) ltac:(reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b848 D_1b848 (zeros 8) (Z_to_bv 64 0)
        ltac:(rdJz) ltac:(reflexivity).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b84c D_1b84c ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b850 D_1b850 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_tk F_1b854 D_1b854 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b934 D_1b934 (word_to_le_bytes 8 (Z_to_bv 64 0x1b9cc)) (Z_to_bv 64 0x1b9cc)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b938 D_1b938 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8))
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b93c D_1b93c (word_to_le_bytes 8 (argcN av)) (argcN av)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b940 D_1b940 (word_to_le_bytes 8 (Z_to_bv 64 0x13ac0)) (Z_to_bv 64 0x13ac0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b944 D_1b944 (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stepret F_1b948 D_1b948 (Z_to_bv 64 0x1b9cc) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1b9cc D_1b9cc.   (* [comment removed for export] *)
      sn F_1b9d0 D_1b9d0.   (* [comment removed for export] *)
      sn F_1b9d4 D_1b9d4.   (* [comment removed for export] *)
      sv F_1b9d8 D_1b9d8 (argcN av).   (* [comment removed for export] *)
      sv F_1b9dc D_1b9dc (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      ld_step F_1b9e0 D_1b9e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b9e4 D_1b9e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b9e8 D_1b9e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b9ec D_1b9ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b9f0 D_1b9f0 (Z_to_bv 64 (bv_unsigned sp0)).   (* [comment removed for export] *)
      stepret F_1b9f4 D_1b9f4 (Z_to_bv 64 0x1b9f8) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sv F_1b9f8 D_1b9f8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).   (* [comment removed for export] *)
      stw F_1b9fc D_1b9fc (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1ba00 D_1ba00 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1ba04 D_1ba04 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr3 Hrr3.
    assert (R2_3 : getr rr3 2 = Z_to_bv 64 (bv_unsigned sp0 - 48)) by (ckv Hrr3).
    assert (R3_3 : getr rr3 3 = Z_to_bv 64 0x10800) by (ckv Hrr3).
    assert (R4_3 : getr rr3 4 = Z_to_bv 64 0x36c60) by (ckv Hrr3).
    assert (R10_3 : getr rr3 10 = Z_to_bv 64 0x13ac0) by (ckv Hrr3).
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
      stw F_1ba08 D_1ba08 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1ba0c D_1ba0c (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).   (* [comment removed for export] *)
      sv F_1ba10 D_1ba10 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      sv F_1ba14 D_1ba14 (argcN av).   (* [comment removed for export] *)
      sn F_1ba18 D_1ba18.   (* [comment removed for export] *)
      stepiv F_1ba1c D_1ba1c (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; exact slli_argc).   (* [comment removed for export] *)
      sv F_1ba20 D_1ba20 (Z_to_bv 64 (bv_unsigned sp0 + 8 * Z.of_nat (length av) + 8)).   (* [comment removed for export] *)
      sv F_1ba24 D_1ba24 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).   (* [comment removed for export] *)
      sn F_1ba28 D_1ba28.   (* [comment removed for export] *)
      sv F_1b94c D_1b94c (Z_to_bv 64 (bv_unsigned sp0 - 80)).   (* [comment removed for export] *)
      stw F_1b950 D_1b950 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 0x1ba2c) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b954 D_1b954 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_1b958 D_1b958 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argcN av) ltac:(ok_win HJ).   (* [comment removed for export] *)
      sn F_1b95c D_1b95c.   (* [comment removed for export] *)
      stepret F_1b71c D_1b71c (Z_to_bv 64 0x1b960) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1b960 D_1b960.   (* [comment removed for export] *)
      sn F_1b964 D_1b964.   (* [comment removed for export] *)
      ld_step F_1b968 D_1b968 (word_to_le_bytes 8 (Z_to_bv 64 0x25730)) (Z_to_bv 64 0x25730)
        ltac:(rdD img_251b0_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b96c D_1b96c (word_to_le_bytes 8 (Z_to_bv 64 0x25728)) (Z_to_bv 64 0x25728)
        ltac:(rdD img_251b8_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_ft F_1b970 D_1b970 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b974 D_1b974 (word_to_le_bytes 8 (Z_to_bv 64 0x139bc)) (Z_to_bv 64 0x139bc)
        ltac:(rdD img_25128_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepjr F_1b978 D_1b978 (Z_to_bv 64 0x139bc) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      sv F_139bc D_139bc (Z_to_bv 64 (bv_unsigned sp0 - 96)).   (* [comment removed for export] *)
      stw F_139c0 D_139c0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 0x1b97c) ltac:(ok_win HJ).   (* [comment removed for export] *)
      stw F_139c4 D_139c4 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 0x25730) ltac:(ok_win HJ).   (* [comment removed for export] *)
      sv F_139c8 D_139c8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).   (* [comment removed for export] *)
      sn F_139cc D_139cc.   (* [comment removed for export] *)
      sn F_139d0 D_139d0.   (* [comment removed for export] *)
      lb_step F_139d4 D_139d4 (Z_to_bv 8 0x0) ltac:(rdD img_264e0_1).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sn F_139d8 D_139d8.   (* [comment removed for export] *)
      apply mst_refl. }
    ckpt rr4 Hrr4.
    assert (R2_4 : getr rr4 2 = Z_to_bv 64 (bv_unsigned sp0 - 96)) by (ckv Hrr4).
    assert (R3_4 : getr rr4 3 = Z_to_bv 64 0x10800) by (ckv Hrr4).
    assert (R4_4 : getr rr4 4 = Z_to_bv 64 0x36c60) by (ckv Hrr4).
    assert (R9_4 : getr rr4 9 = Z_to_bv 64 0x25728) by (ckv Hrr4).
    assert (R10_4 : getr rr4 10 = Z_to_bv 64 0) by (ckv Hrr4).
    assert (R18_4 : getr rr4 18 = Z_to_bv 64 0x13ac0) by (ckv Hrr4).
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
      stepb_tk F_139dc D_139dc ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sn F_139e8 D_139e8.   (* [comment removed for export] *)
      sn F_139ec D_139ec.   (* [comment removed for export] *)
      sn F_139f0 D_139f0.   (* [comment removed for export] *)
      stw F_139f4 D_139f4 (Z_to_bv 64 0x26af0) (Z_to_bv 64 1) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_139f8 D_139f8.   (* [comment removed for export] *)
      ld_step F_139fc D_139fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(rdD img_25168_8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      stepb_tk F_13a00 D_13a00 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_13a20 D_13a20 (word_to_le_bytes 8 (Z_to_bv 64 0x1b97c)) (Z_to_bv 64 0x1b97c)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_13a24 D_13a24 (word_to_le_bytes 8 (Z_to_bv 64 0x25730)) (Z_to_bv 64 0x25730)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_13a28 D_13a28 (Z_to_bv 64 (bv_unsigned sp0 - 80)).   (* [comment removed for export] *)
      stepret F_13a2c D_13a2c (Z_to_bv 64 0x1b97c) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sn F_1b97c D_1b97c.   (* [comment removed for export] *)
      stepb_ft F_1b980 D_1b980 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b984 D_1b984 (word_to_le_bytes 8 (Z_to_bv 64 0x1ba2c)) (Z_to_bv 64 0x1ba2c)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b988 D_1b988 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8))
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      ld_step F_1b98c D_1b98c (word_to_le_bytes 8 (argcN av)) (argcN av)
        ltac:(rdJ) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)   (* [comment removed for export] *)
      sv F_1b990 D_1b990 (Z_to_bv 64 (bv_unsigned sp0 - 48)).   (* [comment removed for export] *)
      stepret F_1b994 D_1b994 (Z_to_bv 64 0x1ba2c) ltac:(pin; reflexivity).   (* [comment removed for export] *)
      sv F_1ba2c D_1ba2c (argcN av).   (* [comment removed for export] *)
      sv F_1ba30 D_1ba30 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      sv F_1ba34 D_1ba34 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).   (* [comment removed for export] *)
      stepjr F_1ba38 D_1ba38 (Z_to_bv 64 0x13ac0) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; gres; pin; first [reflexivity | bveq | f_equal; lia].
  Qed.
End P5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

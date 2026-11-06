(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  StartupTac ArgvEnv RefLayout Es0Img Es0StartupDefs
  Es0_code_r59000_59c90 Es0_code_9b7b0_9ba60.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation RND := (ed_random rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).


  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z.
Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z.
Proof using Hhi. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof using sp0 Hva. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
Proof using sp0 av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
  destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
  unfold rnd_w. repeat split; lia.
Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (at_random_bytes RND))).
Proof using sp0 av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
  intros J D j n Hjn.
  destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
  unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
  rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof using. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    lazymatch goal with
    | |- rdn _ (wbytes (wbytes (wbytes ?DD (Z_to_bv 64 ?g) _) _ _) _ _) _ _ = _ =>
        let H := fresh in
        pose proof (rd_guard_at SEGS DD RND g ltac:(lia) ltac:(lia)) as H;
        cbn [Z.add Pos.add Pos.succ] in H; exact H
    end.


  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
Proof using sp0 Hva.
  pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
  f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 636320 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 963280 ->
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
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 963280) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 962632) ->
getr regs' 13 = (Z_to_bv 64 10) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65600) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x9b838 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x9b7b0 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_9b7b0 D_9b7b0 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_9b7b4 D_9b7b4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 636320) ltac:(ok_win HJ).
stw F_9b7b8 D_9b7b8 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_9b7bc D_9b7bc (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_9b7c0 D_9b7c0 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 963280) ltac:(ok_win HJ).
stw F_9b7c4 D_9b7c4 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_9b7c8 D_9b7c8 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_9b7cc D_9b7cc (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_9b7d0 D_9b7d0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_9b7d4 D_9b7d4.
sn F_9b7d8 D_9b7d8.
sn F_9b7dc D_9b7dc.
sn F_9b7e0 D_9b7e0.
stepb_ft F_9b7e4 D_9b7e4 ltac:(pin; cond_compute).
sn F_9b7e8 D_9b7e8.
sn F_9b7ec D_9b7ec.
sn F_9b7f0 D_9b7f0.
ld_step F_9b7f4 D_9b7f4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9b7f8 D_9b7f8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_9b7fc D_9b7fc.
sn F_9b800 D_9b800.
ld_step F_9b804 D_9b804 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_b9550_4) ltac:(vm_compute; reflexivity).
ld_step F_9b808 D_9b808 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b80c8_8) ltac:(apply bytes_le_to_Z_8).
sn F_9b80c D_9b80c.
sn F_9b810 D_9b810.
sn F_9b814 D_9b814.
sn F_9b818 D_9b818.
sn F_9b81c D_9b81c.
sn F_9b820 D_9b820.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 963280 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 962632 ->
getr regs 13 = Z_to_bv 64 10 ->
getr regs 15 = Z_to_bv 64 65600 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65600 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 963280) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 962632) ->
getr regs' 13 = (Z_to_bv 64 4) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65936) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x9b838 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x9b838 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_9b83c D_9b83c ltac:(pin; cond_compute).
ld_step F_9b824 D_9b824 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_9b828 D_9b828.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 963280 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 962632 ->
getr regs 13 = Z_to_bv 64 4 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65936 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 963280) ->
getr regs' 11 = (Z_to_bv 64 962632) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x9b888 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x9b838 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_ft F_9b860 D_9b860 ltac:(pin; cond_compute).
ld_step F_9b864 D_9b864 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_9b868 D_9b868 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_ft F_9b834 D_9b834 ltac:(pin; cond_compute).
ld_step F_9b838 D_9b838 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9b83c D_9b83c ltac:(pin; cond_compute).
stepb_tk F_9b840 D_9b840 ltac:(pin; cond_compute).
sn F_9b854 D_9b854.
stepb_ft F_9b858 D_9b858 ltac:(pin; cond_compute).
sn F_9b85c D_9b85c.
stepb_tk F_9b860 D_9b860 ltac:(pin; cond_compute).
sn F_9b880 D_9b880.
sn F_9b884 D_9b884.
sn F_9b82c D_9b82c.
sn F_9b830 D_9b830.
stepb_tk F_9b834 D_9b834 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 963280 ->
getr regs 11 = Z_to_bv 64 962632 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 831552) ->
getr regs' 10 = (Z_to_bv 64 962632) ->
getr regs' 11 = (Z_to_bv 64 963336) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 831344) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073708720064) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 831352) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x9ba0c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x9b888 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_9b888 D_9b888 ltac:(pin; cond_compute).
ld_step F_9b8c0 D_9b8c0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_caf38_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9b8c4 D_9b8c4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_caf48_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9b8c8 D_9b8c8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_caf50_8) ltac:(apply bytes_le_to_Z_8).
sn F_9b8cc D_9b8cc.
sn F_9b8d0 D_9b8d0.
sn F_9b8d4 D_9b8d4.
sn F_9b8d8 D_9b8d8.
sn F_9b8dc D_9b8dc.
sn F_9b8e0 D_9b8e0.
sn F_9b8e4 D_9b8e4.
stw F_9b8e8 D_9b8e8 (Z_to_bv 64 962664) (Z_to_bv 64 0) ltac:(ok_data).
stw F_9b8ec D_9b8ec (Z_to_bv 64 962680) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_9b8f0 D_9b8f0 ltac:(pin; cond_compute).
sn F_9b8f4 D_9b8f4.
stw F_9b8f8 D_9b8f8 (Z_to_bv 64 962672) (Z_to_bv 64 8) ltac:(ok_data).
sn F_9b8fc D_9b8fc.
sn F_9b900 D_9b900.
sn F_9b904 D_9b904.
sn F_9b908 D_9b908.
sn F_9b90c D_9b90c.
sn F_9b910 D_9b910.
stw F_9b914 D_9b914 (Z_to_bv 64 963304) (Z_to_bv 64 224) ltac:(ok_data).
stw F_9b918 D_9b918 (Z_to_bv 64 963312) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_9b91c D_9b91c ltac:(pin; cond_compute).
sn F_9b950 D_9b950.
ld_step F_9b954 D_9b954 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_cb310_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9b958 D_9b958 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_cb328_8) ltac:(apply bytes_le_to_Z_8).
sn F_9b95c D_9b95c.
sn F_9b960 D_9b960.
sn F_9b964 D_9b964.
sn F_9b968 D_9b968.
sn F_9b96c D_9b96c.
sn F_9b970 D_9b970.
sn F_9b974 D_9b974.
sn F_9b978 D_9b978.
sn F_9b97c D_9b97c.
sn F_9b980 D_9b980.
sn F_9b984 D_9b984.
stepb_tk F_9b988 D_9b988 ltac:(pin; cond_compute).
stw F_9b9d0 D_9b9d0 (Z_to_bv 64 831568) (Z_to_bv 64 0) ltac:(ok_data).
stw F_9b9d4 D_9b9d4 (Z_to_bv 64 831544) (Z_to_bv 64 831568) ltac:(ok_data).
stw F_9b9d8 D_9b9d8 (Z_to_bv 64 831352) (Z_to_bv 64 831352) ltac:(ok_data).
sn F_9b9dc D_9b9dc.
sn F_9b9e0 D_9b9e0.
sn F_aeb00 D_aeb00.
sn F_aeb04 D_aeb04.
stepret F_aeb08 D_aeb08 (0x9b9e4 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_9b9e4 D_9b9e4 ltac:(pin; cond_compute).
stepb_ft F_9b9e8 D_9b9e8 ltac:(pin; cond_compute).
sn F_9b9ec D_9b9ec.
stw F_9b9f0 D_9b9f0 (Z_to_bv 64 963280) (Z_to_bv 64 1) ltac:(ok_data).
sn F_9b9f4 D_9b9f4.
sn F_9b9f8 D_9b9f8.
stw F_9b9fc D_9b9fc (Z_to_bv 64 831392) (Z_to_bv 64 2) ltac:(ok_data).
sn F_9ba00 D_9ba00.
sn F_9ba04 D_9ba04.
sn F_9ba08 D_9ba08.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 831552 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 963336 ->
getr regs 18 = Z_to_bv 64 831352 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 831552) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x9b5a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x9ba10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_9ba10 D_9ba10.
stw F_9ba14 D_9ba14 (Z_to_bv 64 831384) tid ltac:(ok_data).
stw F_9ba18 D_9ba18 (Z_to_bv 64 831504) (Z_to_bv 64 963336) ltac:(ok_data).
stw F_9ba1c D_9ba1c (Z_to_bv 64 831472) (Z_to_bv 64 831472) ltac:(ok_data).
sn F_9ba20 D_9ba20.
ld_step F_9ba24 D_9ba24 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_cb2e8_8) ltac:(apply bytes_le_to_Z_8).
stw F_9ba28 D_9ba28 (Z_to_bv 64 831360) (Z_to_bv 64 831352) ltac:(ok_data).
stw F_9ba2c D_9ba2c (Z_to_bv 64 831368) (Z_to_bv 64 831352) ltac:(ok_data).
stw F_9ba30 D_9ba30 (Z_to_bv 64 831376) (Z_to_bv 64 0) ltac:(ok_data).
sn F_9ba34 D_9ba34.
ld_step F_9ba3c D_9ba3c (word_to_le_bytes 8 (Z_to_bv 64 636320)) (Z_to_bv 64 636320) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9ba40 D_9ba40 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9ba44 D_9ba44 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9ba48 D_9ba48 (word_to_le_bytes 8 (Z_to_bv 64 963280)) (Z_to_bv 64 963280) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9ba4c D_9ba4c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9ba50 D_9ba50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9ba54 D_9ba54 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_9ba58 D_9ba58 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_9ba5c D_9ba5c (0x9b5a0 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

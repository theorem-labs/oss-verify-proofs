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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  StartupTac ArgvEnv RefLayout Eu0Img Eu0StartupDefs
  Eu0_code_r5a000_5a78c Eu0_code_9d32c_9d5dc.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

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
getr regs 1 = Z_to_bv 64 643356 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 970320 ->
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
getr regs' 9 = (Z_to_bv 64 970320) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 969672) ->
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
G (mkst regs' (0x9d3b4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x9d32c : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_9d32c D_9d32c (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_9d330 D_9d330 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 643356) ltac:(ok_win HJ).
stw F_9d334 D_9d334 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_9d338 D_9d338 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_9d33c D_9d33c (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 970320) ltac:(ok_win HJ).
stw F_9d340 D_9d340 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_9d344 D_9d344 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_9d348 D_9d348 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_9d34c D_9d34c (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_9d350 D_9d350.
sn F_9d354 D_9d354.
sn F_9d358 D_9d358.
sn F_9d35c D_9d35c.
stepb_ft F_9d360 D_9d360 ltac:(pin; cond_compute).
sn F_9d364 D_9d364.
sn F_9d368 D_9d368.
sn F_9d36c D_9d36c.
ld_step F_9d370 D_9d370 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d374 D_9d374 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_9d378 D_9d378.
sn F_9d37c D_9d37c.
ld_step F_9d380 D_9d380 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_bb0c8_4) ltac:(vm_compute; reflexivity).
ld_step F_9d384 D_9d384 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b9c40_8) ltac:(apply bytes_le_to_Z_8).
sn F_9d388 D_9d388.
sn F_9d38c D_9d38c.
sn F_9d390 D_9d390.
sn F_9d394 D_9d394.
sn F_9d398 D_9d398.
sn F_9d39c D_9d39c.
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
getr regs 9 = Z_to_bv 64 970320 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 969672 ->
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
getr regs' 9 = (Z_to_bv 64 970320) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 969672) ->
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
G (mkst regs' (0x9d3b4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x9d3b4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
ld_step F_9d3a0 D_9d3a0 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_9d3a4 D_9d3a4.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 970320 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 969672 ->
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
getr regs' 9 = (Z_to_bv 64 970320) ->
getr regs' 11 = (Z_to_bv 64 969672) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x9d404 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x9d3b4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_ft F_9d3dc D_9d3dc ltac:(pin; cond_compute).
ld_step F_9d3e0 D_9d3e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_9d3e4 D_9d3e4 ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_ft F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
ld_step F_9d3b4 D_9d3b4 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_9d3b8 D_9d3b8 ltac:(pin; cond_compute).
stepb_tk F_9d3bc D_9d3bc ltac:(pin; cond_compute).
sn F_9d3d0 D_9d3d0.
stepb_ft F_9d3d4 D_9d3d4 ltac:(pin; cond_compute).
sn F_9d3d8 D_9d3d8.
stepb_tk F_9d3dc D_9d3dc ltac:(pin; cond_compute).
sn F_9d3fc D_9d3fc.
sn F_9d400 D_9d400.
sn F_9d3a8 D_9d3a8.
sn F_9d3ac D_9d3ac.
stepb_tk F_9d3b0 D_9d3b0 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 970320 ->
getr regs 11 = Z_to_bv 64 969672 ->
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
getr regs' 4 = (Z_to_bv 64 838592) ->
getr regs' 10 = (Z_to_bv 64 969672) ->
getr regs' 11 = (Z_to_bv 64 970376) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 838384) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073708713024) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 838392) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x9d588 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x9d404 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_9d404 D_9d404 ltac:(pin; cond_compute).
ld_step F_9d43c D_9d43c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_ccab8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d440 D_9d440 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_ccac8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d444 D_9d444 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_ccad0_8) ltac:(apply bytes_le_to_Z_8).
sn F_9d448 D_9d448.
sn F_9d44c D_9d44c.
sn F_9d450 D_9d450.
sn F_9d454 D_9d454.
sn F_9d458 D_9d458.
sn F_9d45c D_9d45c.
sn F_9d460 D_9d460.
stw F_9d464 D_9d464 (Z_to_bv 64 969704) (Z_to_bv 64 0) ltac:(ok_data).
stw F_9d468 D_9d468 (Z_to_bv 64 969720) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_9d46c D_9d46c ltac:(pin; cond_compute).
sn F_9d470 D_9d470.
stw F_9d474 D_9d474 (Z_to_bv 64 969712) (Z_to_bv 64 8) ltac:(ok_data).
sn F_9d478 D_9d478.
sn F_9d47c D_9d47c.
sn F_9d480 D_9d480.
sn F_9d484 D_9d484.
sn F_9d488 D_9d488.
sn F_9d48c D_9d48c.
stw F_9d490 D_9d490 (Z_to_bv 64 970344) (Z_to_bv 64 224) ltac:(ok_data).
stw F_9d494 D_9d494 (Z_to_bv 64 970352) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_9d498 D_9d498 ltac:(pin; cond_compute).
sn F_9d4cc D_9d4cc.
ld_step F_9d4d0 D_9d4d0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_cce90_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d4d4 D_9d4d4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_ccea8_8) ltac:(apply bytes_le_to_Z_8).
sn F_9d4d8 D_9d4d8.
sn F_9d4dc D_9d4dc.
sn F_9d4e0 D_9d4e0.
sn F_9d4e4 D_9d4e4.
sn F_9d4e8 D_9d4e8.
sn F_9d4ec D_9d4ec.
sn F_9d4f0 D_9d4f0.
sn F_9d4f4 D_9d4f4.
sn F_9d4f8 D_9d4f8.
sn F_9d4fc D_9d4fc.
sn F_9d500 D_9d500.
stepb_tk F_9d504 D_9d504 ltac:(pin; cond_compute).
stw F_9d54c D_9d54c (Z_to_bv 64 838608) (Z_to_bv 64 0) ltac:(ok_data).
stw F_9d550 D_9d550 (Z_to_bv 64 838584) (Z_to_bv 64 838608) ltac:(ok_data).
stw F_9d554 D_9d554 (Z_to_bv 64 838392) (Z_to_bv 64 838392) ltac:(ok_data).
sn F_9d558 D_9d558.
sn F_9d55c D_9d55c.
sn F_b067c D_b067c.
sn F_b0680 D_b0680.
stepret F_b0684 D_b0684 (0x9d560 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_9d560 D_9d560 ltac:(pin; cond_compute).
stepb_ft F_9d564 D_9d564 ltac:(pin; cond_compute).
sn F_9d568 D_9d568.
stw F_9d56c D_9d56c (Z_to_bv 64 970320) (Z_to_bv 64 1) ltac:(ok_data).
sn F_9d570 D_9d570.
sn F_9d574 D_9d574.
stw F_9d578 D_9d578 (Z_to_bv 64 838432) (Z_to_bv 64 2) ltac:(ok_data).
sn F_9d57c D_9d57c.
sn F_9d580 D_9d580.
sn F_9d584 D_9d584.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 838592 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 970376 ->
getr regs 18 = Z_to_bv 64 838392 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 838592) ->
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
G (mkst regs' (0x9d11c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x9d58c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_9d58c D_9d58c.
stw F_9d590 D_9d590 (Z_to_bv 64 838424) tid ltac:(ok_data).
stw F_9d594 D_9d594 (Z_to_bv 64 838544) (Z_to_bv 64 970376) ltac:(ok_data).
stw F_9d598 D_9d598 (Z_to_bv 64 838512) (Z_to_bv 64 838512) ltac:(ok_data).
sn F_9d59c D_9d59c.
ld_step F_9d5a0 D_9d5a0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_cce68_8) ltac:(apply bytes_le_to_Z_8).
stw F_9d5a4 D_9d5a4 (Z_to_bv 64 838400) (Z_to_bv 64 838392) ltac:(ok_data).
stw F_9d5a8 D_9d5a8 (Z_to_bv 64 838408) (Z_to_bv 64 838392) ltac:(ok_data).
stw F_9d5ac D_9d5ac (Z_to_bv 64 838416) (Z_to_bv 64 0) ltac:(ok_data).
sn F_9d5b0 D_9d5b0.
ld_step F_9d5b8 D_9d5b8 (word_to_le_bytes 8 (Z_to_bv 64 643356)) (Z_to_bv 64 643356) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d5bc D_9d5bc (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d5c0 D_9d5c0 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d5c4 D_9d5c4 (word_to_le_bytes 8 (Z_to_bv 64 970320)) (Z_to_bv 64 970320) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d5c8 D_9d5c8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d5cc D_9d5cc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_9d5d0 D_9d5d0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_9d5d4 D_9d5d4 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_9d5d8 D_9d5d8 (0x9d11c : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

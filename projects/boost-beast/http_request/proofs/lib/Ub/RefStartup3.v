(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import StartupTac ArgvEnv RefLayout Ub_code_6b580_6b830 Ub_code_79454_79c00 Ub_code_7cbe0_7cd30.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefImgTls RefStartupDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd)) (only parsing).

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 438936) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 8 = (pn_w sp0 av ev) ->
getr regs 9 = s1v ->
getr regs 10 = (Z_to_bv 64 (bv_unsigned sp0 - 368)) ->
getr regs 18 = (Z_to_bv 64 748544) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 438936) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (pn_w sp0 av ev) ->
getr regs' 9 = (Z_to_bv 64 748544) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 747896) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 11) ->
getr regs' 14 = (Z_to_bv 64 546240) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 18 = (Z_to_bv 64 748544) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
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
G (mkst regs' (0x6b608 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x6b580 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_6b580 D_6b580 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_6b584 D_6b584 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 438936) ltac:(ok_win HJ).
stw F_6b588 D_6b588 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_6b58c D_6b58c (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_6b590 D_6b590 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 748544) ltac:(ok_win HJ).
stw F_6b594 D_6b594 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_6b598 D_6b598 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_6b59c D_6b59c (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_6b5a0 D_6b5a0 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6b5a4 D_6b5a4.
sn F_6b5a8 D_6b5a8.
sn F_6b5ac D_6b5ac.
sn F_6b5b0 D_6b5b0.
stepb_ft F_6b5b4 D_6b5b4 ltac:(pin; cond_compute).
sn F_6b5b8 D_6b5b8.
sn F_6b5bc D_6b5bc.
sn F_6b5c0 D_6b5c0.
ld_step F_6b5c4 D_6b5c4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b5c8 D_6b5c8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6b5cc D_6b5cc.
sn F_6b5d0 D_6b5d0.
ld_step F_6b5d4 D_6b5d4 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_84f28_4) ltac:(vm_compute; reflexivity).
ld_step F_6b5d8 D_6b5d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_83a00_8) ltac:(apply bytes_le_to_Z_8).
sn F_6b5dc D_6b5dc.
sn F_6b5e0 D_6b5e0.
sn F_6b5e4 D_6b5e4.
sn F_6b5e8 D_6b5e8.
sn F_6b5ec D_6b5ec.
sn F_6b5f0 D_6b5f0.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 438936) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 6 = (Z_to_bv 64 2) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 8 = (pn_w sp0 av ev) ->
getr regs 9 = (Z_to_bv 64 748544) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 747896) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 13 = (Z_to_bv 64 11) ->
getr regs 14 = (Z_to_bv 64 546240) ->
getr regs 15 = (Z_to_bv 64 65600) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 17 = (Z_to_bv 64 0) ->
getr regs 18 = (Z_to_bv 64 748544) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
getr regs 28 = (Z_to_bv 64 1685382481) ->
getr regs 29 = (Z_to_bv 64 65600) ->
getr regs 30 = (Z_to_bv 64 131072) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 438936) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (Z_to_bv 64 1) ->
getr regs' 9 = (Z_to_bv 64 748544) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 747896) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 6) ->
getr regs' 14 = (Z_to_bv 64 546240) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 18 = (Z_to_bv 64 748544) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65880) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
getr regs' 31 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x6b608 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x6b608 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_6b60c D_6b60c ltac:(pin; cond_compute).
ld_step F_6b5f4 D_6b5f4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_6b5f8 D_6b5f8.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 438936) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 6 = (Z_to_bv 64 2) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 8 = (Z_to_bv 64 1) ->
getr regs 9 = (Z_to_bv 64 748544) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 747896) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 13 = (Z_to_bv 64 6) ->
getr regs 14 = (Z_to_bv 64 546240) ->
getr regs 15 = (Z_to_bv 64 65600) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 17 = (Z_to_bv 64 0) ->
getr regs 18 = (Z_to_bv 64 748544) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
getr regs 28 = (Z_to_bv 64 1685382481) ->
getr regs 29 = (Z_to_bv 64 65880) ->
getr regs 30 = (Z_to_bv 64 131072) ->
getr regs 31 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 438936) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (Z_to_bv 64 1879048195) ->
getr regs' 9 = (Z_to_bv 64 748544) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 747896) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 0) ->
getr regs' 14 = (Z_to_bv 64 546240) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 65880) ->
getr regs' 18 = (Z_to_bv 64 748544) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 66216) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
getr regs' 31 = (Z_to_bv 64 65880) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x6b658 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x6b608 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_tk F_6b628 D_6b628 ltac:(pin; cond_compute).
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_ft F_6b630 D_6b630 ltac:(pin; cond_compute).
ld_step F_6b634 D_6b634 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_10228_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_6b638 D_6b638 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_ft F_6b604 D_6b604 ltac:(pin; cond_compute).
ld_step F_6b608 D_6b608 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10270_4) ltac:(vm_compute; reflexivity).
stepb_ft F_6b60c D_6b60c ltac:(pin; cond_compute).
stepb_tk F_6b610 D_6b610 ltac:(pin; cond_compute).
sn F_6b624 D_6b624.
stepb_ft F_6b628 D_6b628 ltac:(pin; cond_compute).
sn F_6b62c D_6b62c.
stepb_tk F_6b630 D_6b630 ltac:(pin; cond_compute).
sn F_6b650 D_6b650.
sn F_6b654 D_6b654.
sn F_6b5fc D_6b5fc.
sn F_6b600 D_6b600.
stepb_tk F_6b604 D_6b604 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 438936) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 6 = (Z_to_bv 64 2) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 8 = (Z_to_bv 64 1879048195) ->
getr regs 9 = (Z_to_bv 64 748544) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 747896) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 13 = (Z_to_bv 64 0) ->
getr regs 14 = (Z_to_bv 64 546240) ->
getr regs 15 = (Z_to_bv 64 65600) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 17 = (Z_to_bv 64 65880) ->
getr regs 18 = (Z_to_bv 64 748544) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
getr regs 28 = (Z_to_bv 64 1685382481) ->
getr regs 29 = (Z_to_bv 64 66216) ->
getr regs 30 = (Z_to_bv 64 131072) ->
getr regs 31 = (Z_to_bv 64 65880) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 440244) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 616816) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (Z_to_bv 64 616816) ->
getr regs' 9 = (Z_to_bv 64 748544) ->
getr regs' 10 = (Z_to_bv 64 747896) ->
getr regs' 11 = (Z_to_bv 64 748600) ->
getr regs' 12 = (Z_to_bv 64 1) ->
getr regs' 13 = (Z_to_bv 64 616816) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 0) ->
getr regs' 16 = (Z_to_bv 64 0) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 616616) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 616832) ->
getr regs' 21 = (Z_to_bv 64 616848) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 66216) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
getr regs' 31 = (Z_to_bv 64 65880) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x6b7dc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x6b658 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_ft F_6b658 D_6b658 ltac:(pin; cond_compute).
sn F_6b65c D_6b65c.
ld_step F_6b660 D_6b660 (word_to_le_bytes 8 (Z_to_bv 64 513104)) (Z_to_bv 64 513104) ltac:(rd_img img_10168_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b664 D_6b664 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_10178_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b668 D_6b668 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rd_img img_10180_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b66c D_6b66c (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rd_img img_10188_8) ltac:(apply bytes_le_to_Z_8).
sn F_6b670 D_6b670.
sn F_6b674 D_6b674.
stw F_6b678 D_6b678 (Z_to_bv 64 747912) (Z_to_bv 64 513104) ltac:(ok_data).
stw F_6b67c D_6b67c (Z_to_bv 64 747920) (Z_to_bv 64 0) ltac:(ok_data).
stw F_6b680 D_6b680 (Z_to_bv 64 747936) (Z_to_bv 64 8) ltac:(ok_data).
stw F_6b684 D_6b684 (Z_to_bv 64 748560) (Z_to_bv 64 747904) ltac:(ok_data).
stw F_6b688 D_6b688 (Z_to_bv 64 748584) (Z_to_bv 64 1) ltac:(ok_data).
sn F_6b68c D_6b68c.
sn F_6b69c D_6b69c.
sn F_6b6a0 D_6b6a0.
sn F_6b6a4 D_6b6a4.
sn F_6b6a8 D_6b6a8.
sn F_6b6ac D_6b6ac.
sn F_6b6b0 D_6b6b0.
sn F_6b6b4 D_6b6b4.
stw F_6b6b8 D_6b6b8 (Z_to_bv 64 747928) (Z_to_bv 64 8) ltac:(ok_data).
stw F_6b6bc D_6b6bc (Z_to_bv 64 747944) (Z_to_bv 64 0) ltac:(ok_data).
stepb_tk F_6b6c0 D_6b6c0 ltac:(pin; cond_compute).
sn F_6b6cc D_6b6cc.
sn F_6b6d0 D_6b6d0.
sn F_6b6d4 D_6b6d4.
sn F_6b6d8 D_6b6d8.
sn F_6b6dc D_6b6dc.
sn F_6b6e0 D_6b6e0.
stw F_6b6e4 D_6b6e4 (Z_to_bv 64 748568) (Z_to_bv 64 232) ltac:(ok_data).
stw F_6b6e8 D_6b6e8 (Z_to_bv 64 748576) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_6b6ec D_6b6ec ltac:(pin; cond_compute).
sn F_6b720 D_6b720.
ld_step F_6b724 D_6b724 (word_to_le_bytes 8 (Z_to_bv 64 747904)) (Z_to_bv 64 747904) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b728 D_6b728 (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6b72c D_6b72c.
sn F_6b730 D_6b730.
sn F_6b734 D_6b734.
sn F_6b738 D_6b738.
sn F_6b73c D_6b73c.
sn F_6b740 D_6b740.
sn F_6b744 D_6b744.
sn F_6b748 D_6b748.
sn F_6b74c D_6b74c.
sn F_6b750 D_6b750.
sn F_6b754 D_6b754.
stepb_ft F_6b758 D_6b758 ltac:(pin; cond_compute).
sn F_6b75c D_6b75c.
sn F_6b760 D_6b760.
sn F_6b764 D_6b764.
ld_step F_6b768 D_6b768 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6b76c D_6b76c.
sn F_6b770 D_6b770.
sn F_6b774 D_6b774.
stw F_6b778 D_6b778 (Z_to_bv 64 616840) (Z_to_bv 64 618864) ltac:(ok_data).
ld_step F_6b77c D_6b77c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b780 D_6b780 (word_to_le_bytes 8 (Z_to_bv 64 513104)) (Z_to_bv 64 513104) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b784 D_6b784 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6b788 D_6b788.
sn F_6b78c D_6b78c.
sn F_79550 D_79550.
stepb_tk F_79554 D_79554 ltac:(pin; cond_compute).
sn F_79664 D_79664.
sn F_79668 D_79668.
stepb_ft F_7966c D_7966c ltac:(pin; cond_compute).
sn F_79670 D_79670.
stepb_tk F_79674 D_79674 ltac:(pin; cond_compute).
sn F_796ac D_796ac.
stepb_tk F_796b0 D_796b0 ltac:(pin; cond_compute).
sn F_796cc D_796cc.
stepb_tk F_796d0 D_796d0 ltac:(pin; cond_compute).
sn F_79910 D_79910.
stepb_ft F_79914 D_79914 ltac:(pin; cond_compute).
sn F_79918 D_79918.
stepb_ft F_7991c D_7991c ltac:(pin; cond_compute).
stepret F_79920 D_79920 (0x6b790 : word) ltac:(pin; first [reflexivity | bveq]).
ld_step F_6b790 D_6b790 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b6980_8) ltac:(apply bytes_le_to_Z_8).
sn F_6b794 D_6b794.
stepb_ft F_6b798 D_6b798 ltac:(pin; cond_compute).
ld_step F_6b79c D_6b79c (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stw F_6b7a0 D_6b7a0 (Z_to_bv 64 616832) (Z_to_bv 64 1) ltac:(ok_data).
stw F_6b7a4 D_6b7a4 (Z_to_bv 64 616808) (Z_to_bv 64 616832) ltac:(ok_data).
stw F_6b7a8 D_6b7a8 (Z_to_bv 64 616616) (Z_to_bv 64 616616) ltac:(ok_data).
sn F_6b7ac D_6b7ac.
sn F_6b7b0 D_6b7b0.
sn F_7cbe0 D_7cbe0.
sn F_7cbe4 D_7cbe4.
stepret F_7cbe8 D_7cbe8 (0x6b7b4 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_6b7b4 D_6b7b4 ltac:(pin; cond_compute).
stepb_ft F_6b7b8 D_6b7b8 ltac:(pin; cond_compute).
sn F_6b7bc D_6b7bc.
stw F_6b7c0 D_6b7c0 (Z_to_bv 64 748544) (Z_to_bv 64 1) ltac:(ok_data).
sn F_6b7c4 D_6b7c4.
sn F_6b7c8 D_6b7c8.
stw F_6b7cc D_6b7cc (Z_to_bv 64 616656) (Z_to_bv 64 2) ltac:(ok_data).
sn F_6b7d0 D_6b7d0.
sn F_6b7d4 D_6b7d4.
sn F_6b7d8 D_6b7d8.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 4 = (Z_to_bv 64 616816) ->
getr regs 10 = tid ->
getr regs 11 = (Z_to_bv 64 748600) ->
getr regs 18 = (Z_to_bv 64 616616) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 438936) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 616816) ->
getr regs' 8 = (pn_w sp0 av ev) ->
getr regs' 9 = s1v ->
getr regs' 10 = (Z_to_bv 64 0) ->
getr regs' 11 = (Z_to_bv 64 748600) ->
getr regs' 12 = (Z_to_bv 64 616736) ->
getr regs' 18 = (Z_to_bv 64 748544) ->
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
G (mkst regs' (0x6b298 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x6b7e0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_6b7e0 D_6b7e0.
stw F_6b7e4 D_6b7e4 (Z_to_bv 64 616648) tid ltac:(ok_data).
stw F_6b7e8 D_6b7e8 (Z_to_bv 64 616768) (Z_to_bv 64 748600) ltac:(ok_data).
stw F_6b7ec D_6b7ec (Z_to_bv 64 616736) (Z_to_bv 64 616736) ltac:(ok_data).
sn F_6b7f0 D_6b7f0.
ld_step F_6b7f4 D_6b7f4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b6be8_8) ltac:(apply bytes_le_to_Z_8).
stw F_6b7f8 D_6b7f8 (Z_to_bv 64 616624) (Z_to_bv 64 616616) ltac:(ok_data).
stw F_6b7fc D_6b7fc (Z_to_bv 64 616632) (Z_to_bv 64 616616) ltac:(ok_data).
stw F_6b800 D_6b800 (Z_to_bv 64 616640) (Z_to_bv 64 0) ltac:(ok_data).
sn F_6b804 D_6b804.
ld_step F_6b80c D_6b80c (word_to_le_bytes 8 (Z_to_bv 64 438936)) (Z_to_bv 64 438936) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b810 D_6b810 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b814 D_6b814 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b818 D_6b818 (word_to_le_bytes 8 (Z_to_bv 64 748544)) (Z_to_bv 64 748544) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b81c D_6b81c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b820 D_6b820 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6b824 D_6b824 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_6b828 D_6b828 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_6b82c D_6b82c (0x6b298 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

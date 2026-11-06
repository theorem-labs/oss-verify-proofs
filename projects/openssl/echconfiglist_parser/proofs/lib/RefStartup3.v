(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs Ref_code_26e688_26f1d8 Ref_code_27d7b4_27d7c0        .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

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
getr regs 1 = Z_to_bv 64 2549732 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 3208968 ->
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
getr regs' 9 = (Z_to_bv 64 3208968) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 3208320) ->
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
G (mkst regs' (0x26eb54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x26eacc : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_26ea84 D_26ea84 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
stw F_26ea88 D_26ea88 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 2549732) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_26ea8c D_26ea8c (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_26ea90 D_26ea90 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_26ea94 D_26ea94 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 3208968) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_26ea98 D_26ea98 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_26ea9c D_26ea9c (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_26eaa0 D_26eaa0 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
ld_step F_26eaa4 D_26eaa4 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_26eaa8 D_26eaa8.  (* [comment removed for export] *)
sn F_26eaac D_26eaac.  (* [comment removed for export] *)
sn F_26eab0 D_26eab0.  (* [comment removed for export] *)
sn F_26eab4 D_26eab4.  (* [comment removed for export] *)
stepb_ft F_26eab8 D_26eab8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eabc D_26eabc.  (* [comment removed for export] *)
sn F_26eac0 D_26eac0.  (* [comment removed for export] *)
sn F_26eac4 D_26eac4.  (* [comment removed for export] *)
ld_step F_26eac8 D_26eac8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26eacc D_26eacc (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_26ead0 D_26ead0.  (* [comment removed for export] *)
sn F_26ead4 D_26ead4.  (* [comment removed for export] *)
ld_step F_26ead8 D_26ead8 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_2dc858_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
ld_step F_26eadc D_26eadc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2daaf0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_26eae0 D_26eae0.  (* [comment removed for export] *)
sn F_26eae4 D_26eae4.  (* [comment removed for export] *)
sn F_26eae8 D_26eae8.  (* [comment removed for export] *)
sn F_26eaec D_26eaec.  (* [comment removed for export] *)
sn F_26eaf0 D_26eaf0.  (* [comment removed for export] *)
sn F_26eaf4 D_26eaf4.  (* [comment removed for export] *)
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
getr regs 9 = Z_to_bv 64 3208968 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 3208320 ->
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
getr regs' 9 = (Z_to_bv 64 3208968) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 3208320) ->
getr regs' 13 = (Z_to_bv 64 5) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65880) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x26eb54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x26eb54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_tk F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eaf8 D_26eaf8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_26eafc D_26eafc.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
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
getr regs 9 = Z_to_bv 64 3208968 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 3208320 ->
getr regs 13 = Z_to_bv 64 5 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65880 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 3208968) ->
getr regs' 11 = (Z_to_bv 64 3208320) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x26eba4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x26eb54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_ft F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb38 D_26eb38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
stepb_tk F_26eb3c D_26eb3c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_ft F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb0c D_26eb0c (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_26eb10 D_26eb10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_26eb14 D_26eb14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb28 D_26eb28.  (* [comment removed for export] *)
stepb_ft F_26eb2c D_26eb2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb30 D_26eb30.  (* [comment removed for export] *)
stepb_tk F_26eb34 D_26eb34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26eb54 D_26eb54.  (* [comment removed for export] *)
sn F_26eb58 D_26eb58.  (* [comment removed for export] *)
sn F_26eb00 D_26eb00.  (* [comment removed for export] *)
sn F_26eb04 D_26eb04.  (* [comment removed for export] *)
stepb_tk F_26eb08 D_26eb08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 3208968 ->
getr regs 11 = Z_to_bv 64 3208320 ->
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
getr regs' 4 = (Z_to_bv 64 3077240) ->
getr regs' 8 = (Z_to_bv 64 3077240) ->
getr regs' 10 = (Z_to_bv 64 3208320) ->
getr regs' 11 = (Z_to_bv 64 3209024) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 3077032) ->
getr regs' 15 = (Z_to_bv 64 18446744073706474376) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 3077040) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 3077256) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x26ed28 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x26eba4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_26eb5c D_26eb5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_26eb94 D_26eb94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ef380_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26eb98 D_26eb98 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ef390_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26eb9c D_26eb9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ef398_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_26eba0 D_26eba0.  (* [comment removed for export] *)
sn F_26eba4 D_26eba4.  (* [comment removed for export] *)
sn F_26eba8 D_26eba8.  (* [comment removed for export] *)
sn F_26ebac D_26ebac.  (* [comment removed for export] *)
sn F_26ebb0 D_26ebb0.  (* [comment removed for export] *)
sn F_26ebb4 D_26ebb4.  (* [comment removed for export] *)
sn F_26ebb8 D_26ebb8.  (* [comment removed for export] *)
stw F_26ebbc D_26ebbc (Z_to_bv 64 0x30f4a0) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stw F_26ebc0 D_26ebc0 (Z_to_bv 64 0x30f4b0) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stepb_ft F_26ebc4 D_26ebc4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26ebc8 D_26ebc8.  (* [comment removed for export] *)
stw F_26ebcc D_26ebcc (Z_to_bv 64 0x30f4a8) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
sn F_26ebd0 D_26ebd0.  (* [comment removed for export] *)
sn F_26ebd4 D_26ebd4.  (* [comment removed for export] *)
sn F_26ebd8 D_26ebd8.  (* [comment removed for export] *)
sn F_26ebdc D_26ebdc.  (* [comment removed for export] *)
sn F_26ebe0 D_26ebe0.  (* [comment removed for export] *)
sn F_26ebe4 D_26ebe4.
stw F_26ebe8 D_26ebe8 (Z_to_bv 64 0x30f720) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
stw F_26ebec D_26ebec (Z_to_bv 64 0x30f728) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
stepb_tk F_26ebf0 D_26ebf0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26ec24 D_26ec24.  (* [comment removed for export] *)
ld_step F_26ec28 D_26ec28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ef758_8) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      (* [comment removed for export] *)
ld_step F_26ec2c D_26ec2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ef770_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_26ec30 D_26ec30.
      (* [comment removed for export] *)
sn F_26ec34 D_26ec34.  (* [comment removed for export] *)
sn F_26ec38 D_26ec38.  (* [comment removed for export] *)
sn F_26ec3c D_26ec3c.  (* [comment removed for export] *)
sn F_26ec40 D_26ec40.  (* [comment removed for export] *)
sn F_26ec44 D_26ec44.  (* [comment removed for export] *)
sn F_26ec48 D_26ec48.  (* [comment removed for export] *)
sn F_26ec4c D_26ec4c.  (* [comment removed for export] *)
sn F_26ec50 D_26ec50.  (* [comment removed for export] *)
sn F_26ec54 D_26ec54.  (* [comment removed for export] *)
sn F_26ec58 D_26ec58.  (* [comment removed for export] *)
stepb_tk F_26ec5c D_26ec5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
stw F_26eca4 D_26eca4 (Z_to_bv 64 0x2ef488) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stw F_26eca8 D_26eca8 (Z_to_bv 64 0x2ef470) (Z_to_bv 64 0x2ef488) ltac:(ok_data).  (* [comment removed for export] *)
stw F_26ecac D_26ecac (Z_to_bv 64 0x2ef3b0) (Z_to_bv 64 0x2ef3b0) ltac:(ok_data).  (* [comment removed for export] *)
sn F_26ecb0 D_26ecb0.  (* [comment removed for export] *)
sn F_26ecb4 D_26ecb4.  (* [comment removed for export] *)
sn F_27d7b4 D_27d7b4.  (* [comment removed for export] *)
sn F_27d7b8 D_27d7b8.  (* [comment removed for export] *)
stepret F_27d7bc D_27d7bc (0x26ed00 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
stepb_ft F_26ecb8 D_26ecb8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_ft F_26ecbc D_26ecbc ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_26ecc0 D_26ecc0.  (* [comment removed for export] *)
stw F_26ecc4 D_26ecc4 (Z_to_bv 64 0x30f708) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
sn F_26ecc8 D_26ecc8.  (* [comment removed for export] *)
sn F_26eccc D_26eccc.  (* [comment removed for export] *)
stw F_26ecd0 D_26ecd0 (Z_to_bv 64 0x2ef3d8) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
sn F_26ecd4 D_26ecd4.  (* [comment removed for export] *)
sn F_26ecd8 D_26ecd8.  (* [comment removed for export] *)
sn F_26ecdc D_26ecdc.  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 3077240 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 3209024 ->
getr regs 18 = Z_to_bv 64 3077040 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 3077240) ->
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
G (mkst regs' (0x26e7e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x26ed2c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_26ece4 D_26ece4.  (* [comment removed for export] *)
stw F_26ece8 D_26ece8 (Z_to_bv 64 3077072) tid ltac:(ok_data).  (* [comment removed for export] *)
stw F_26ecec D_26ecec (Z_to_bv 64 3077192) (Z_to_bv 64 3209024) ltac:(ok_data).  (* [comment removed for export] *)
stw F_26ecf0 D_26ecf0 (Z_to_bv 64 3077160) (Z_to_bv 64 3077160) ltac:(ok_data).  (* [comment removed for export] *)
sn F_26ecf4 D_26ecf4.  (* [comment removed for export] *)
ld_step F_26ecf8 D_26ecf8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ef730_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
stw F_26ecfc D_26ecfc (Z_to_bv 64 3077048) (Z_to_bv 64 3077040) ltac:(ok_data).  (* [comment removed for export] *)
stw F_26ed00 D_26ed00 (Z_to_bv 64 3077056) (Z_to_bv 64 3077040) ltac:(ok_data).  (* [comment removed for export] *)
stw F_26ed04 D_26ed04 (Z_to_bv 64 3077064) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
sn F_26ed08 D_26ed08.  (* [comment removed for export] *)
ld_step F_26ed10 D_26ed10 (word_to_le_bytes 8 (Z_to_bv 64 2549732)) (Z_to_bv 64 2549732) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26ed14 D_26ed14 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26ed18 D_26ed18 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26ed1c D_26ed1c (word_to_le_bytes 8 (Z_to_bv 64 3208968)) (Z_to_bv 64 3208968) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26ed20 D_26ed20 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26ed24 D_26ed24 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_26ed28 D_26ed28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sv F_26ed2c D_26ed2c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
stepret F_26ed30 D_26ed30 (0x26e7e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

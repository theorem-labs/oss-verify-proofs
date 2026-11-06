(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import UStartupImg UStartupDefs UStartupCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
#[local] Existing Instance fx0.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 88660 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 347224 ->
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
getr regs' 9 = (Z_to_bv 64 347224) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 346584) ->
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
G (mkst regs' (0x15cec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x15c64 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_15c64 D_15c64 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_15c68 D_15c68 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 88660) ltac:(ok_win HJ).
stw F_15c6c D_15c6c (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_15c70 D_15c70 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_15c74 D_15c74 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 347224) ltac:(ok_win HJ).
stw F_15c78 D_15c78 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_15c7c D_15c7c (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_15c80 D_15c80 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_15c84 D_15c84 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_15c88 D_15c88.
sn F_15c8c D_15c8c.
sn F_15c90 D_15c90.
sn F_15c94 D_15c94.
stepb_ft F_15c98 D_15c98 ltac:(pin; cond_compute).
sn F_15c9c D_15c9c.
sn F_15ca0 D_15ca0.
sn F_15ca4 D_15ca4.
ld_step F_15ca8 D_15ca8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15cac D_15cac (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_15cb0 D_15cb0.
sn F_15cb4 D_15cb4.
ld_step F_15cb8 D_15cb8 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_24868_4) ltac:(vm_compute; reflexivity).
ld_step F_15cbc D_15cbc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_235b8_8) ltac:(apply bytes_le_to_Z_8).
sn F_15cc0 D_15cc0.
sn F_15cc4 D_15cc4.
sn F_15cc8 D_15cc8.
sn F_15ccc D_15ccc.
sn F_15cd0 D_15cd0.
sn F_15cd4 D_15cd4.
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
getr regs 9 = Z_to_bv 64 347224 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 346584 ->
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
getr regs' 9 = (Z_to_bv 64 347224) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 346584) ->
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
G (mkst regs' (0x15cec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x15cec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_15cf0 D_15cf0 ltac:(pin; cond_compute).
ld_step F_15cd8 D_15cd8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_15cdc D_15cdc.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 347224 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 346584 ->
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
getr regs' 9 = (Z_to_bv 64 347224) ->
getr regs' 11 = (Z_to_bv 64 346584) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x15d3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x15cec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_ft F_15d14 D_15d14 ltac:(pin; cond_compute).
ld_step F_15d18 D_15d18 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_15d1c D_15d1c ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_ft F_15ce8 D_15ce8 ltac:(pin; cond_compute).
ld_step F_15cec D_15cec (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_15cf0 D_15cf0 ltac:(pin; cond_compute).
stepb_tk F_15cf4 D_15cf4 ltac:(pin; cond_compute).
sn F_15d08 D_15d08.
stepb_ft F_15d0c D_15d0c ltac:(pin; cond_compute).
sn F_15d10 D_15d10.
stepb_tk F_15d14 D_15d14 ltac:(pin; cond_compute).
sn F_15d34 D_15d34.
sn F_15d38 D_15d38.
sn F_15ce0 D_15ce0.
sn F_15ce4 D_15ce4.
stepb_tk F_15ce8 D_15ce8 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 347224 ->
getr regs 11 = Z_to_bv 64 346584 ->
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
getr regs' 4 = (Z_to_bv 64 215504) ->
getr regs' 10 = (Z_to_bv 64 346584) ->
getr regs' 11 = (Z_to_bv 64 347280) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 215296) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709336112) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 215304) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x15ec0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x15d3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_15d3c D_15d3c ltac:(pin; cond_compute).
ld_step F_15d74 D_15d74 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_549e8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15d78 D_15d78 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_549f8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15d7c D_15d7c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_54a00_8) ltac:(apply bytes_le_to_Z_8).
sn F_15d80 D_15d80.
sn F_15d84 D_15d84.
sn F_15d88 D_15d88.
sn F_15d8c D_15d8c.
sn F_15d90 D_15d90.
sn F_15d94 D_15d94.
sn F_15d98 D_15d98.
stw F_15d9c D_15d9c (Z_to_bv 64 346616) (Z_to_bv 64 0) ltac:(ok_data).
stw F_15da0 D_15da0 (Z_to_bv 64 346632) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_15da4 D_15da4 ltac:(pin; cond_compute).
sn F_15da8 D_15da8.
stw F_15dac D_15dac (Z_to_bv 64 346624) (Z_to_bv 64 8) ltac:(ok_data).
sn F_15db0 D_15db0.
sn F_15db4 D_15db4.
sn F_15db8 D_15db8.
sn F_15dbc D_15dbc.
sn F_15dc0 D_15dc0.
sn F_15dc4 D_15dc4.
stw F_15dc8 D_15dc8 (Z_to_bv 64 347248) (Z_to_bv 64 224) ltac:(ok_data).
stw F_15dcc D_15dcc (Z_to_bv 64 347256) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_15dd0 D_15dd0 ltac:(pin; cond_compute).
sn F_15e04 D_15e04.
ld_step F_15e08 D_15e08 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_54c68_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15e0c D_15e0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_54c80_8) ltac:(apply bytes_le_to_Z_8).
sn F_15e10 D_15e10.
sn F_15e14 D_15e14.
sn F_15e18 D_15e18.
sn F_15e1c D_15e1c.
sn F_15e20 D_15e20.
sn F_15e24 D_15e24.
sn F_15e28 D_15e28.
sn F_15e2c D_15e2c.
sn F_15e30 D_15e30.
sn F_15e34 D_15e34.
sn F_15e38 D_15e38.
stepb_tk F_15e3c D_15e3c ltac:(pin; cond_compute).
stw F_15e84 D_15e84 (Z_to_bv 64 215520) (Z_to_bv 64 0) ltac:(ok_data).
stw F_15e88 D_15e88 (Z_to_bv 64 215496) (Z_to_bv 64 215520) ltac:(ok_data).
stw F_15e8c D_15e8c (Z_to_bv 64 215304) (Z_to_bv 64 215304) ltac:(ok_data).
sn F_15e90 D_15e90.
sn F_15e94 D_15e94.
sn F_22480 D_22480.
sn F_22484 D_22484.
stepret F_22488 D_22488 (0x15e98 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_15e98 D_15e98 ltac:(pin; cond_compute).
stepb_ft F_15e9c D_15e9c ltac:(pin; cond_compute).
sn F_15ea0 D_15ea0.
stw F_15ea4 D_15ea4 (Z_to_bv 64 347224) (Z_to_bv 64 1) ltac:(ok_data).
sn F_15ea8 D_15ea8.
sn F_15eac D_15eac.
stw F_15eb0 D_15eb0 (Z_to_bv 64 215344) (Z_to_bv 64 2) ltac:(ok_data).
sn F_15eb4 D_15eb4.
sn F_15eb8 D_15eb8.
sn F_15ebc D_15ebc.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 215504 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 347280 ->
getr regs 18 = Z_to_bv 64 215304 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 215504) ->
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
G (mkst regs' (0x15a54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x15ec4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_15ec4 D_15ec4.
stw F_15ec8 D_15ec8 (Z_to_bv 64 215336) tid ltac:(ok_data).
stw F_15ecc D_15ecc (Z_to_bv 64 215456) (Z_to_bv 64 347280) ltac:(ok_data).
stw F_15ed0 D_15ed0 (Z_to_bv 64 215424) (Z_to_bv 64 215424) ltac:(ok_data).
sn F_15ed4 D_15ed4.
ld_step F_15ed8 D_15ed8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_54c40_8) ltac:(apply bytes_le_to_Z_8).
stw F_15edc D_15edc (Z_to_bv 64 215312) (Z_to_bv 64 215304) ltac:(ok_data).
stw F_15ee0 D_15ee0 (Z_to_bv 64 215320) (Z_to_bv 64 215304) ltac:(ok_data).
stw F_15ee4 D_15ee4 (Z_to_bv 64 215328) (Z_to_bv 64 0) ltac:(ok_data).
sn F_15ee8 D_15ee8.
ld_step F_15ef0 D_15ef0 (word_to_le_bytes 8 (Z_to_bv 64 88660)) (Z_to_bv 64 88660) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15ef4 D_15ef4 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15ef8 D_15ef8 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15efc D_15efc (word_to_le_bytes 8 (Z_to_bv 64 347224)) (Z_to_bv 64 347224) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15f00 D_15f00 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15f04 D_15f04 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_15f08 D_15f08 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_15f0c D_15f0c (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_15f10 D_15f10 (0x15a54 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

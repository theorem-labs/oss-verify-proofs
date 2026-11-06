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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PStartupImg PStartupDefs PStartupCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
#[local] Existing Instance fx0.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

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
getr regs 1 = Z_to_bv 64 84240 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 342808 ->
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
getr regs' 9 = (Z_to_bv 64 342808) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 342168) ->
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
G (mkst regs' (0x14ba8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x14b20 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_14b20 D_14b20 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_14b24 D_14b24 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 84240) ltac:(ok_win HJ).
stw F_14b28 D_14b28 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_14b2c D_14b2c (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_14b30 D_14b30 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 342808) ltac:(ok_win HJ).
stw F_14b34 D_14b34 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_14b38 D_14b38 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_14b3c D_14b3c (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_14b40 D_14b40 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_14b44 D_14b44.
sn F_14b48 D_14b48.
sn F_14b4c D_14b4c.
sn F_14b50 D_14b50.
stepb_ft F_14b54 D_14b54 ltac:(pin; cond_compute).
sn F_14b58 D_14b58.
sn F_14b5c D_14b5c.
sn F_14b60 D_14b60.
ld_step F_14b64 D_14b64 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14b68 D_14b68 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_14b6c D_14b6c.
sn F_14b70 D_14b70.
ld_step F_14b74 D_14b74 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_23720_4) ltac:(vm_compute; reflexivity).
ld_step F_14b78 D_14b78 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22470_8) ltac:(apply bytes_le_to_Z_8).
sn F_14b7c D_14b7c.
sn F_14b80 D_14b80.
sn F_14b84 D_14b84.
sn F_14b88 D_14b88.
sn F_14b8c D_14b8c.
sn F_14b90 D_14b90.
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
getr regs 9 = Z_to_bv 64 342808 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 342168 ->
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
getr regs' 9 = (Z_to_bv 64 342808) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 342168) ->
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
G (mkst regs' (0x14ba8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x14ba8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_14bac D_14bac ltac:(pin; cond_compute).
ld_step F_14b94 D_14b94 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_14b98 D_14b98.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 342808 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 342168 ->
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
getr regs' 9 = (Z_to_bv 64 342808) ->
getr regs' 11 = (Z_to_bv 64 342168) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x14bf8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x14ba8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_ft F_14bd0 D_14bd0 ltac:(pin; cond_compute).
ld_step F_14bd4 D_14bd4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_14bd8 D_14bd8 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_ft F_14ba4 D_14ba4 ltac:(pin; cond_compute).
ld_step F_14ba8 D_14ba8 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_14bac D_14bac ltac:(pin; cond_compute).
stepb_tk F_14bb0 D_14bb0 ltac:(pin; cond_compute).
sn F_14bc4 D_14bc4.
stepb_ft F_14bc8 D_14bc8 ltac:(pin; cond_compute).
sn F_14bcc D_14bcc.
stepb_tk F_14bd0 D_14bd0 ltac:(pin; cond_compute).
sn F_14bf0 D_14bf0.
sn F_14bf4 D_14bf4.
sn F_14b9c D_14b9c.
sn F_14ba0 D_14ba0.
stepb_tk F_14ba4 D_14ba4 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 342808 ->
getr regs 11 = Z_to_bv 64 342168 ->
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
getr regs' 4 = (Z_to_bv 64 211088) ->
getr regs' 10 = (Z_to_bv 64 342168) ->
getr regs' 11 = (Z_to_bv 64 342864) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 210880) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709340528) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 210888) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x14d7c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x14bf8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_14bf8 D_14bf8 ltac:(pin; cond_compute).
ld_step F_14c30 D_14c30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_538a8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14c34 D_14c34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_538b8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14c38 D_14c38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_538c0_8) ltac:(apply bytes_le_to_Z_8).
sn F_14c3c D_14c3c.
sn F_14c40 D_14c40.
sn F_14c44 D_14c44.
sn F_14c48 D_14c48.
sn F_14c4c D_14c4c.
sn F_14c50 D_14c50.
sn F_14c54 D_14c54.
stw F_14c58 D_14c58 (Z_to_bv 64 342200) (Z_to_bv 64 0) ltac:(ok_data).
stw F_14c5c D_14c5c (Z_to_bv 64 342216) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_14c60 D_14c60 ltac:(pin; cond_compute).
sn F_14c64 D_14c64.
stw F_14c68 D_14c68 (Z_to_bv 64 342208) (Z_to_bv 64 8) ltac:(ok_data).
sn F_14c6c D_14c6c.
sn F_14c70 D_14c70.
sn F_14c74 D_14c74.
sn F_14c78 D_14c78.
sn F_14c7c D_14c7c.
sn F_14c80 D_14c80.
stw F_14c84 D_14c84 (Z_to_bv 64 342832) (Z_to_bv 64 224) ltac:(ok_data).
stw F_14c88 D_14c88 (Z_to_bv 64 342840) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_14c8c D_14c8c ltac:(pin; cond_compute).
sn F_14cc0 D_14cc0.
ld_step F_14cc4 D_14cc4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_53b28_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14cc8 D_14cc8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_53b40_8) ltac:(apply bytes_le_to_Z_8).
sn F_14ccc D_14ccc.
sn F_14cd0 D_14cd0.
sn F_14cd4 D_14cd4.
sn F_14cd8 D_14cd8.
sn F_14cdc D_14cdc.
sn F_14ce0 D_14ce0.
sn F_14ce4 D_14ce4.
sn F_14ce8 D_14ce8.
sn F_14cec D_14cec.
sn F_14cf0 D_14cf0.
sn F_14cf4 D_14cf4.
stepb_tk F_14cf8 D_14cf8 ltac:(pin; cond_compute).
stw F_14d40 D_14d40 (Z_to_bv 64 211104) (Z_to_bv 64 0) ltac:(ok_data).
stw F_14d44 D_14d44 (Z_to_bv 64 211080) (Z_to_bv 64 211104) ltac:(ok_data).
stw F_14d48 D_14d48 (Z_to_bv 64 210888) (Z_to_bv 64 210888) ltac:(ok_data).
sn F_14d4c D_14d4c.
sn F_14d50 D_14d50.
sn F_2133c D_2133c.
sn F_21340 D_21340.
stepret F_21344 D_21344 (0x14d54 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_14d54 D_14d54 ltac:(pin; cond_compute).
stepb_ft F_14d58 D_14d58 ltac:(pin; cond_compute).
sn F_14d5c D_14d5c.
stw F_14d60 D_14d60 (Z_to_bv 64 342808) (Z_to_bv 64 1) ltac:(ok_data).
sn F_14d64 D_14d64.
sn F_14d68 D_14d68.
stw F_14d6c D_14d6c (Z_to_bv 64 210928) (Z_to_bv 64 2) ltac:(ok_data).
sn F_14d70 D_14d70.
sn F_14d74 D_14d74.
sn F_14d78 D_14d78.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 211088 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 342864 ->
getr regs 18 = Z_to_bv 64 210888 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 211088) ->
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
G (mkst regs' (0x14910 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x14d80 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_14d80 D_14d80.
stw F_14d84 D_14d84 (Z_to_bv 64 210920) tid ltac:(ok_data).
stw F_14d88 D_14d88 (Z_to_bv 64 211040) (Z_to_bv 64 342864) ltac:(ok_data).
stw F_14d8c D_14d8c (Z_to_bv 64 211008) (Z_to_bv 64 211008) ltac:(ok_data).
sn F_14d90 D_14d90.
ld_step F_14d94 D_14d94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_53b00_8) ltac:(apply bytes_le_to_Z_8).
stw F_14d98 D_14d98 (Z_to_bv 64 210896) (Z_to_bv 64 210888) ltac:(ok_data).
stw F_14d9c D_14d9c (Z_to_bv 64 210904) (Z_to_bv 64 210888) ltac:(ok_data).
stw F_14da0 D_14da0 (Z_to_bv 64 210912) (Z_to_bv 64 0) ltac:(ok_data).
sn F_14da4 D_14da4.
ld_step F_14dac D_14dac (word_to_le_bytes 8 (Z_to_bv 64 84240)) (Z_to_bv 64 84240) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14db0 D_14db0 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14db4 D_14db4 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14db8 D_14db8 (word_to_le_bytes 8 (Z_to_bv 64 342808)) (Z_to_bv 64 342808) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14dbc D_14dbc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14dc0 D_14dc0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_14dc4 D_14dc4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_14dc8 D_14dc8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_14dcc D_14dcc (0x14910 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

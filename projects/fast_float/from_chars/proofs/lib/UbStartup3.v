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
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StartupTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.StartupTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbImg UbStartupDefs Ub_code_22780_228cc Ub_code_5233c_52dd8 Ub_code_60628_60720 Ub_code_61234_61240 Ub_code_memcpy Ub_code_52660_52910.
Import ListNotations.
Open Scope bv_scope.
Local Instance clf_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

#[using="Hlo Hhi"] Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 336976 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 621600 ->
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
getr regs' 9 = (Z_to_bv 64 621600) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 620952) ->
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
G (mkst regs' (0x526e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x52660 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo Hhi : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_52660 D_52660 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_52664 D_52664 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 336976) ltac:(ok_win HJ).
stw F_52668 D_52668 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_5266c D_5266c (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_52670 D_52670 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 621600) ltac:(ok_win HJ).
stw F_52674 D_52674 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_52678 D_52678 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_5267c D_5267c (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_52680 D_52680 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_52684 D_52684.
sn F_52688 D_52688.
sn F_5268c D_5268c.
sn F_52690 D_52690.
stepb_ft F_52694 D_52694 ltac:(pin; cond_compute).
sn F_52698 D_52698.
sn F_5269c D_5269c.
sn F_526a0 D_526a0.
ld_step F_526a4 D_526a4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_526a8 D_526a8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_526ac D_526ac.
sn F_526b0 D_526b0.
ld_step F_526b4 D_526b4 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_66db8_4) ltac:(vm_compute; reflexivity).
ld_step F_526b8 D_526b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_65a20_8) ltac:(apply bytes_le_to_Z_8).
sn F_526bc D_526bc.
sn F_526c0 D_526c0.
sn F_526c4 D_526c4.
sn F_526c8 D_526c8.
sn F_526cc D_526cc.
sn F_526d0 D_526d0.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 621600 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 620952 ->
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
getr regs' 9 = (Z_to_bv 64 621600) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 620952) ->
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
G (mkst regs' (0x526e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x526e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_526ec D_526ec ltac:(pin; cond_compute).
ld_step F_526d4 D_526d4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_526d8 D_526d8.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 621600 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 620952 ->
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
getr regs' 9 = (Z_to_bv 64 621600) ->
getr regs' 11 = (Z_to_bv 64 620952) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x52738 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x526e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_ft F_52710 D_52710 ltac:(pin; cond_compute).
ld_step F_52714 D_52714 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_52718 D_52718 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_ft F_526e4 D_526e4 ltac:(pin; cond_compute).
ld_step F_526e8 D_526e8 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_526ec D_526ec ltac:(pin; cond_compute).
stepb_tk F_526f0 D_526f0 ltac:(pin; cond_compute).
sn F_52704 D_52704.
stepb_ft F_52708 D_52708 ltac:(pin; cond_compute).
sn F_5270c D_5270c.
stepb_tk F_52710 D_52710 ltac:(pin; cond_compute).
sn F_52730 D_52730.
sn F_52734 D_52734.
sn F_526dc D_526dc.
sn F_526e0 D_526e0.
stepb_tk F_526e4 D_526e4 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 621600 ->
getr regs 11 = Z_to_bv 64 620952 ->
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
getr regs' 4 = (Z_to_bv 64 489872) ->
getr regs' 10 = (Z_to_bv 64 620952) ->
getr regs' 11 = (Z_to_bv 64 621656) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 489664) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709061744) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 489672) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x528bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x52738 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_52738 D_52738 ltac:(pin; cond_compute).
ld_step F_52770 D_52770 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_979a8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_52774 D_52774 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_979b8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_52778 D_52778 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_979c0_8) ltac:(apply bytes_le_to_Z_8).
sn F_5277c D_5277c.
sn F_52780 D_52780.
sn F_52784 D_52784.
sn F_52788 D_52788.
sn F_5278c D_5278c.
sn F_52790 D_52790.
sn F_52794 D_52794.
stw F_52798 D_52798 (Z_to_bv 64 620984) (Z_to_bv 64 0) ltac:(ok_data).
stw F_5279c D_5279c (Z_to_bv 64 621000) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_527a0 D_527a0 ltac:(pin; cond_compute).
sn F_527a4 D_527a4.
stw F_527a8 D_527a8 (Z_to_bv 64 620992) (Z_to_bv 64 8) ltac:(ok_data).
sn F_527ac D_527ac.
sn F_527b0 D_527b0.
sn F_527b4 D_527b4.
sn F_527b8 D_527b8.
sn F_527bc D_527bc.
sn F_527c0 D_527c0.
stw F_527c4 D_527c4 (Z_to_bv 64 621624) (Z_to_bv 64 224) ltac:(ok_data).
stw F_527c8 D_527c8 (Z_to_bv 64 621632) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_527cc D_527cc ltac:(pin; cond_compute).
sn F_52800 D_52800.
ld_step F_52804 D_52804 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_97c30_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_52808 D_52808 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_97c48_8) ltac:(apply bytes_le_to_Z_8).
sn F_5280c D_5280c.
sn F_52810 D_52810.
sn F_52814 D_52814.
sn F_52818 D_52818.
sn F_5281c D_5281c.
sn F_52820 D_52820.
sn F_52824 D_52824.
sn F_52828 D_52828.
sn F_5282c D_5282c.
sn F_52830 D_52830.
sn F_52834 D_52834.
stepb_tk F_52838 D_52838 ltac:(pin; cond_compute).
stw F_52880 D_52880 (Z_to_bv 64 489888) (Z_to_bv 64 0) ltac:(ok_data).
stw F_52884 D_52884 (Z_to_bv 64 489864) (Z_to_bv 64 489888) ltac:(ok_data).
stw F_52888 D_52888 (Z_to_bv 64 489672) (Z_to_bv 64 489672) ltac:(ok_data).
sn F_5288c D_5288c.
sn F_52890 D_52890.
sn F_61234 D_61234.
sn F_61238 D_61238.
stepret F_6123c D_6123c (0x52894 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_52894 D_52894 ltac:(pin; cond_compute).
stepb_ft F_52898 D_52898 ltac:(pin; cond_compute).
sn F_5289c D_5289c.
stw F_528a0 D_528a0 (Z_to_bv 64 621600) (Z_to_bv 64 1) ltac:(ok_data).
sn F_528a4 D_528a4.
sn F_528a8 D_528a8.
stw F_528ac D_528ac (Z_to_bv 64 489712) (Z_to_bv 64 2) ltac:(ok_data).
sn F_528b0 D_528b0.
sn F_528b4 D_528b4.
sn F_528b8 D_528b8.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo Hhi"] Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 489872 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 621656 ->
getr regs 18 = Z_to_bv 64 489672 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 489872) ->
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
G (mkst regs' (0x52450 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x528c0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof. LiaFast.lf_pins (fun (Hlo Hhi : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_528c0 D_528c0.
stw F_528c4 D_528c4 (Z_to_bv 64 489704) tid ltac:(ok_data).
stw F_528c8 D_528c8 (Z_to_bv 64 489824) (Z_to_bv 64 621656) ltac:(ok_data).
stw F_528cc D_528cc (Z_to_bv 64 489792) (Z_to_bv 64 489792) ltac:(ok_data).
sn F_528d0 D_528d0.
ld_step F_528d4 D_528d4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_97c08_8) ltac:(apply bytes_le_to_Z_8).
stw F_528d8 D_528d8 (Z_to_bv 64 489680) (Z_to_bv 64 489672) ltac:(ok_data).
stw F_528dc D_528dc (Z_to_bv 64 489688) (Z_to_bv 64 489672) ltac:(ok_data).
stw F_528e0 D_528e0 (Z_to_bv 64 489696) (Z_to_bv 64 0) ltac:(ok_data).
sn F_528e4 D_528e4.
ld_step F_528ec D_528ec (word_to_le_bytes 8 (Z_to_bv 64 336976)) (Z_to_bv 64 336976) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_528f0 D_528f0 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_528f4 D_528f4 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_528f8 D_528f8 (word_to_le_bytes 8 (Z_to_bv 64 621600)) (Z_to_bv 64 621600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_528fc D_528fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_52900 D_52900 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_52904 D_52904 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_52908 D_52908 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_5290c D_5290c (0x52450 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

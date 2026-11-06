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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StartupTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.StartupTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefImg RefStartupDefs Ref_code_224ec_22638 Ref_code_50584_51020 Ref_code_5e870_5e968 Ref_code_5f47c_5f488 Ref_code_memcpy Ref_code_508a8_50b58.
Import ListNotations.
Open Scope bv_scope.
Local Instance clf_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

#[using="Hlo Hhi"] Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 329368 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 613984 ->
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
getr regs' 9 = (Z_to_bv 64 613984) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 613336) ->
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
G (mkst regs' (0x50930 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x508a8 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo Hhi : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_508a8 D_508a8 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_508ac D_508ac (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 329368) ltac:(ok_win HJ).
stw F_508b0 D_508b0 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_508b4 D_508b4 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_508b8 D_508b8 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 613984) ltac:(ok_win HJ).
stw F_508bc D_508bc (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_508c0 D_508c0 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_508c4 D_508c4 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_508c8 D_508c8 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_508cc D_508cc.
sn F_508d0 D_508d0.
sn F_508d4 D_508d4.
sn F_508d8 D_508d8.
stepb_ft F_508dc D_508dc ltac:(pin; cond_compute).
sn F_508e0 D_508e0.
sn F_508e4 D_508e4.
sn F_508e8 D_508e8.
ld_step F_508ec D_508ec (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_508f0 D_508f0 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_508f4 D_508f4.
sn F_508f8 D_508f8.
ld_step F_508fc D_508fc (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_65000_4) ltac:(vm_compute; reflexivity).
ld_step F_50900 D_50900 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_63c68_8) ltac:(apply bytes_le_to_Z_8).
sn F_50904 D_50904.
sn F_50908 D_50908.
sn F_5090c D_5090c.
sn F_50910 D_50910.
sn F_50914 D_50914.
sn F_50918 D_50918.
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
getr regs 9 = Z_to_bv 64 613984 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 613336 ->
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
getr regs' 9 = (Z_to_bv 64 613984) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 613336) ->
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
G (mkst regs' (0x50930 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x50930 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_50934 D_50934 ltac:(pin; cond_compute).
ld_step F_5091c D_5091c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_50920 D_50920.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 613984 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 613336 ->
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
getr regs' 9 = (Z_to_bv 64 613984) ->
getr regs' 11 = (Z_to_bv 64 613336) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x50980 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x50930 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_ft F_50958 D_50958 ltac:(pin; cond_compute).
ld_step F_5095c D_5095c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_50960 D_50960 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_ft F_5092c D_5092c ltac:(pin; cond_compute).
ld_step F_50930 D_50930 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_50934 D_50934 ltac:(pin; cond_compute).
stepb_tk F_50938 D_50938 ltac:(pin; cond_compute).
sn F_5094c D_5094c.
stepb_ft F_50950 D_50950 ltac:(pin; cond_compute).
sn F_50954 D_50954.
stepb_tk F_50958 D_50958 ltac:(pin; cond_compute).
sn F_50978 D_50978.
sn F_5097c D_5097c.
sn F_50924 D_50924.
sn F_50928 D_50928.
stepb_tk F_5092c D_5092c ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 613984 ->
getr regs 11 = Z_to_bv 64 613336 ->
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
getr regs' 4 = (Z_to_bv 64 482256) ->
getr regs' 10 = (Z_to_bv 64 613336) ->
getr regs' 11 = (Z_to_bv 64 614040) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 482048) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709069360) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 482056) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x50b04 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x50980 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_50980 D_50980 ltac:(pin; cond_compute).
ld_step F_509b8 D_509b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_95be8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_509bc D_509bc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_95bf8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_509c0 D_509c0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_95c00_8) ltac:(apply bytes_le_to_Z_8).
sn F_509c4 D_509c4.
sn F_509c8 D_509c8.
sn F_509cc D_509cc.
sn F_509d0 D_509d0.
sn F_509d4 D_509d4.
sn F_509d8 D_509d8.
sn F_509dc D_509dc.
stw F_509e0 D_509e0 (Z_to_bv 64 613368) (Z_to_bv 64 0) ltac:(ok_data).
stw F_509e4 D_509e4 (Z_to_bv 64 613384) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_509e8 D_509e8 ltac:(pin; cond_compute).
sn F_509ec D_509ec.
stw F_509f0 D_509f0 (Z_to_bv 64 613376) (Z_to_bv 64 8) ltac:(ok_data).
sn F_509f4 D_509f4.
sn F_509f8 D_509f8.
sn F_509fc D_509fc.
sn F_50a00 D_50a00.
sn F_50a04 D_50a04.
sn F_50a08 D_50a08.
stw F_50a0c D_50a0c (Z_to_bv 64 614008) (Z_to_bv 64 224) ltac:(ok_data).
stw F_50a10 D_50a10 (Z_to_bv 64 614016) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_50a14 D_50a14 ltac:(pin; cond_compute).
sn F_50a48 D_50a48.
ld_step F_50a4c D_50a4c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_95e70_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_50a50 D_50a50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_95e88_8) ltac:(apply bytes_le_to_Z_8).
sn F_50a54 D_50a54.
sn F_50a58 D_50a58.
sn F_50a5c D_50a5c.
sn F_50a60 D_50a60.
sn F_50a64 D_50a64.
sn F_50a68 D_50a68.
sn F_50a6c D_50a6c.
sn F_50a70 D_50a70.
sn F_50a74 D_50a74.
sn F_50a78 D_50a78.
sn F_50a7c D_50a7c.
stepb_tk F_50a80 D_50a80 ltac:(pin; cond_compute).
stw F_50ac8 D_50ac8 (Z_to_bv 64 482272) (Z_to_bv 64 0) ltac:(ok_data).
stw F_50acc D_50acc (Z_to_bv 64 482248) (Z_to_bv 64 482272) ltac:(ok_data).
stw F_50ad0 D_50ad0 (Z_to_bv 64 482056) (Z_to_bv 64 482056) ltac:(ok_data).
sn F_50ad4 D_50ad4.
sn F_50ad8 D_50ad8.
sn F_5f47c D_5f47c.
sn F_5f480 D_5f480.
stepret F_5f484 D_5f484 (0x50adc : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_50adc D_50adc ltac:(pin; cond_compute).
stepb_ft F_50ae0 D_50ae0 ltac:(pin; cond_compute).
sn F_50ae4 D_50ae4.
stw F_50ae8 D_50ae8 (Z_to_bv 64 613984) (Z_to_bv 64 1) ltac:(ok_data).
sn F_50aec D_50aec.
sn F_50af0 D_50af0.
stw F_50af4 D_50af4 (Z_to_bv 64 482096) (Z_to_bv 64 2) ltac:(ok_data).
sn F_50af8 D_50af8.
sn F_50afc D_50afc.
sn F_50b00 D_50b00.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo Hhi"] Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 482256 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 614040 ->
getr regs 18 = Z_to_bv 64 482056 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 482256) ->
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
G (mkst regs' (0x50698 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x50b08 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof. LiaFast.lf_pins (fun (Hlo Hhi : LiaFast.U) => LiaFast.u0).
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_50b08 D_50b08.
stw F_50b0c D_50b0c (Z_to_bv 64 482088) tid ltac:(ok_data).
stw F_50b10 D_50b10 (Z_to_bv 64 482208) (Z_to_bv 64 614040) ltac:(ok_data).
stw F_50b14 D_50b14 (Z_to_bv 64 482176) (Z_to_bv 64 482176) ltac:(ok_data).
sn F_50b18 D_50b18.
ld_step F_50b1c D_50b1c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_95e48_8) ltac:(apply bytes_le_to_Z_8).
stw F_50b20 D_50b20 (Z_to_bv 64 482064) (Z_to_bv 64 482056) ltac:(ok_data).
stw F_50b24 D_50b24 (Z_to_bv 64 482072) (Z_to_bv 64 482056) ltac:(ok_data).
stw F_50b28 D_50b28 (Z_to_bv 64 482080) (Z_to_bv 64 0) ltac:(ok_data).
sn F_50b2c D_50b2c.
ld_step F_50b34 D_50b34 (word_to_le_bytes 8 (Z_to_bv 64 329368)) (Z_to_bv 64 329368) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_50b38 D_50b38 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_50b3c D_50b3c (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_50b40 D_50b40 (word_to_le_bytes 8 (Z_to_bv 64 613984)) (Z_to_bv 64 613984) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_50b44 D_50b44 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_50b48 D_50b48 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_50b4c D_50b4c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_50b50 D_50b50 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_50b54 D_50b54 (0x50698 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

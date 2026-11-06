(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  StartupTac ArgvEnv RefLayout RefImgTls RefStartupDefs Ref_code_67254_67504 Ref_code_788b4_78a04 Ref_code_75128_758d4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
getr regs 1 = (Z_to_bv 64 421740) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 8 = (pn_w sp0 av ev) ->
getr regs 9 = s1v ->
getr regs 10 = (Z_to_bv 64 (bv_unsigned sp0 - 368)) ->
getr regs 18 = (Z_to_bv 64 731360) ->
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
getr regs' 1 = (Z_to_bv 64 421740) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (pn_w sp0 av ev) ->
getr regs' 9 = (Z_to_bv 64 731360) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 730712) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 11) ->
getr regs' 14 = (Z_to_bv 64 529044) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 18 = (Z_to_bv 64 731360) ->
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
G (mkst regs' (0x672dc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x67254 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_67254 D_67254 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_67258 D_67258 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 421740) ltac:(ok_win HJ).
stw F_6725c D_6725c (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_67260 D_67260 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_67264 D_67264 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 731360) ltac:(ok_win HJ).
stw F_67268 D_67268 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_6726c D_6726c (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_67270 D_67270 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_67274 D_67274 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_67278 D_67278.
sn F_6727c D_6727c.
sn F_67280 D_67280.
sn F_67284 D_67284.
stepb_ft F_67288 D_67288 ltac:(pin; cond_compute).
sn F_6728c D_6728c.
sn F_67290 D_67290.
sn F_67294 D_67294.
ld_step F_67298 D_67298 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6729c D_6729c (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_672a0 D_672a0.
sn F_672a4 D_672a4.
ld_step F_672a8 D_672a8 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_80c00_4) ltac:(vm_compute; reflexivity).
ld_step F_672ac D_672ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_7f6d8_8) ltac:(apply bytes_le_to_Z_8).
sn F_672b0 D_672b0.
sn F_672b4 D_672b4.
sn F_672b8 D_672b8.
sn F_672bc D_672bc.
sn F_672c0 D_672c0.
sn F_672c4 D_672c4.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 421740) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 6 = (Z_to_bv 64 2) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 8 = (pn_w sp0 av ev) ->
getr regs 9 = (Z_to_bv 64 731360) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 730712) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 13 = (Z_to_bv 64 11) ->
getr regs 14 = (Z_to_bv 64 529044) ->
getr regs 15 = (Z_to_bv 64 65600) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 17 = (Z_to_bv 64 0) ->
getr regs 18 = (Z_to_bv 64 731360) ->
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
getr regs' 1 = (Z_to_bv 64 421740) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (Z_to_bv 64 1) ->
getr regs' 9 = (Z_to_bv 64 731360) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 730712) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 6) ->
getr regs' 14 = (Z_to_bv 64 529044) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 18 = (Z_to_bv 64 731360) ->
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
G (mkst regs' (0x672dc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x672dc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_672e0 D_672e0 ltac:(pin; cond_compute).
ld_step F_672c8 D_672c8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_672cc D_672cc.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 421740) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 6 = (Z_to_bv 64 2) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 8 = (Z_to_bv 64 1) ->
getr regs 9 = (Z_to_bv 64 731360) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 730712) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 13 = (Z_to_bv 64 6) ->
getr regs 14 = (Z_to_bv 64 529044) ->
getr regs 15 = (Z_to_bv 64 65600) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 17 = (Z_to_bv 64 0) ->
getr regs 18 = (Z_to_bv 64 731360) ->
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
getr regs' 1 = (Z_to_bv 64 421740) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (Z_to_bv 64 1879048195) ->
getr regs' 9 = (Z_to_bv 64 731360) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 730712) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 0) ->
getr regs' 14 = (Z_to_bv 64 529044) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 65880) ->
getr regs' 18 = (Z_to_bv 64 731360) ->
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
G (mkst regs' (0x6732c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x672dc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_tk F_672fc D_672fc ltac:(pin; cond_compute).
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_ft F_67304 D_67304 ltac:(pin; cond_compute).
ld_step F_67308 D_67308 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_10228_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_6730c D_6730c ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_ft F_672d8 D_672d8 ltac:(pin; cond_compute).
ld_step F_672dc D_672dc (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10270_4) ltac:(vm_compute; reflexivity).
stepb_ft F_672e0 D_672e0 ltac:(pin; cond_compute).
stepb_tk F_672e4 D_672e4 ltac:(pin; cond_compute).
sn F_672f8 D_672f8.
stepb_ft F_672fc D_672fc ltac:(pin; cond_compute).
sn F_67300 D_67300.
stepb_tk F_67304 D_67304 ltac:(pin; cond_compute).
sn F_67324 D_67324.
sn F_67328 D_67328.
sn F_672d0 D_672d0.
sn F_672d4 D_672d4.
stepb_tk F_672d8 D_672d8 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 421740) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 6 = (Z_to_bv 64 2) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 8 = (Z_to_bv 64 1879048195) ->
getr regs 9 = (Z_to_bv 64 731360) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 730712) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 13 = (Z_to_bv 64 0) ->
getr regs 14 = (Z_to_bv 64 529044) ->
getr regs 15 = (Z_to_bv 64 65600) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 17 = (Z_to_bv 64 65880) ->
getr regs 18 = (Z_to_bv 64 731360) ->
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
getr regs' 1 = (Z_to_bv 64 423048) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 599632) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 6 = (Z_to_bv 64 2) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 8 = (Z_to_bv 64 599632) ->
getr regs' 9 = (Z_to_bv 64 731360) ->
getr regs' 10 = (Z_to_bv 64 730712) ->
getr regs' 11 = (Z_to_bv 64 731416) ->
getr regs' 12 = (Z_to_bv 64 1) ->
getr regs' 13 = (Z_to_bv 64 599632) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 0) ->
getr regs' 16 = (Z_to_bv 64 0) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 599432) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 599648) ->
getr regs' 21 = (Z_to_bv 64 599664) ->
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
G (mkst regs' (0x674b0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x6732c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_ft F_6732c D_6732c ltac:(pin; cond_compute).
sn F_67330 D_67330.
ld_step F_67334 D_67334 (word_to_le_bytes 8 (Z_to_bv 64 495912)) (Z_to_bv 64 495912) ltac:(rd_img img_10168_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_67338 D_67338 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_10178_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6733c D_6733c (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rd_img img_10180_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_67340 D_67340 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rd_img img_10188_8) ltac:(apply bytes_le_to_Z_8).
sn F_67344 D_67344.
sn F_67348 D_67348.
stw F_6734c D_6734c (Z_to_bv 64 730728) (Z_to_bv 64 495912) ltac:(ok_data).
stw F_67350 D_67350 (Z_to_bv 64 730736) (Z_to_bv 64 0) ltac:(ok_data).
stw F_67354 D_67354 (Z_to_bv 64 730752) (Z_to_bv 64 8) ltac:(ok_data).
stw F_67358 D_67358 (Z_to_bv 64 731376) (Z_to_bv 64 730720) ltac:(ok_data).
stw F_6735c D_6735c (Z_to_bv 64 731400) (Z_to_bv 64 1) ltac:(ok_data).
sn F_67360 D_67360.
sn F_67370 D_67370.
sn F_67374 D_67374.
sn F_67378 D_67378.
sn F_6737c D_6737c.
sn F_67380 D_67380.
sn F_67384 D_67384.
sn F_67388 D_67388.
stw F_6738c D_6738c (Z_to_bv 64 730744) (Z_to_bv 64 8) ltac:(ok_data).
stw F_67390 D_67390 (Z_to_bv 64 730760) (Z_to_bv 64 0) ltac:(ok_data).
stepb_tk F_67394 D_67394 ltac:(pin; cond_compute).
sn F_673a0 D_673a0.
sn F_673a4 D_673a4.
sn F_673a8 D_673a8.
sn F_673ac D_673ac.
sn F_673b0 D_673b0.
sn F_673b4 D_673b4.
stw F_673b8 D_673b8 (Z_to_bv 64 731384) (Z_to_bv 64 232) ltac:(ok_data).
stw F_673bc D_673bc (Z_to_bv 64 731392) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_673c0 D_673c0 ltac:(pin; cond_compute).
sn F_673f4 D_673f4.
ld_step F_673f8 D_673f8 (word_to_le_bytes 8 (Z_to_bv 64 730720)) (Z_to_bv 64 730720) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_673fc D_673fc (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_67400 D_67400.
sn F_67404 D_67404.
sn F_67408 D_67408.
sn F_6740c D_6740c.
sn F_67410 D_67410.
sn F_67414 D_67414.
sn F_67418 D_67418.
sn F_6741c D_6741c.
sn F_67420 D_67420.
sn F_67424 D_67424.
sn F_67428 D_67428.
stepb_ft F_6742c D_6742c ltac:(pin; cond_compute).
sn F_67430 D_67430.
sn F_67434 D_67434.
sn F_67438 D_67438.
ld_step F_6743c D_6743c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_67440 D_67440.
sn F_67444 D_67444.
sn F_67448 D_67448.
stw F_6744c D_6744c (Z_to_bv 64 599656) (Z_to_bv 64 601680) ltac:(ok_data).
ld_step F_67450 D_67450 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_67454 D_67454 (word_to_le_bytes 8 (Z_to_bv 64 495912)) (Z_to_bv 64 495912) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_67458 D_67458 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6745c D_6745c.
sn F_67460 D_67460.
sn F_75224 D_75224.
stepb_tk F_75228 D_75228 ltac:(pin; cond_compute).
sn F_75338 D_75338.
sn F_7533c D_7533c.
stepb_ft F_75340 D_75340 ltac:(pin; cond_compute).
sn F_75344 D_75344.
stepb_tk F_75348 D_75348 ltac:(pin; cond_compute).
sn F_75380 D_75380.
stepb_tk F_75384 D_75384 ltac:(pin; cond_compute).
sn F_753a0 D_753a0.
stepb_tk F_753a4 D_753a4 ltac:(pin; cond_compute).
sn F_755e4 D_755e4.
stepb_ft F_755e8 D_755e8 ltac:(pin; cond_compute).
sn F_755ec D_755ec.
stepb_ft F_755f0 D_755f0 ltac:(pin; cond_compute).
stepret F_755f4 D_755f4 (0x67464 : word) ltac:(pin; first [reflexivity | bveq]).
ld_step F_67464 D_67464 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b2660_8) ltac:(apply bytes_le_to_Z_8).
sn F_67468 D_67468.
stepb_ft F_6746c D_6746c ltac:(pin; cond_compute).
ld_step F_67470 D_67470 (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rewrite rdn_cmem_data by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stw F_67474 D_67474 (Z_to_bv 64 599648) (Z_to_bv 64 1) ltac:(ok_data).
stw F_67478 D_67478 (Z_to_bv 64 599624) (Z_to_bv 64 599648) ltac:(ok_data).
stw F_6747c D_6747c (Z_to_bv 64 599432) (Z_to_bv 64 599432) ltac:(ok_data).
sn F_67480 D_67480.
sn F_67484 D_67484.
sn F_788b4 D_788b4.
sn F_788b8 D_788b8.
stepret F_788bc D_788bc (0x67488 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_67488 D_67488 ltac:(pin; cond_compute).
stepb_ft F_6748c D_6748c ltac:(pin; cond_compute).
sn F_67490 D_67490.
stw F_67494 D_67494 (Z_to_bv 64 731360) (Z_to_bv 64 1) ltac:(ok_data).
sn F_67498 D_67498.
sn F_6749c D_6749c.
stw F_674a0 D_674a0 (Z_to_bv 64 599472) (Z_to_bv 64 2) ltac:(ok_data).
sn F_674a4 D_674a4.
sn F_674a8 D_674a8.
sn F_674ac D_674ac.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 67584) ->
getr regs 4 = (Z_to_bv 64 599632) ->
getr regs 10 = tid ->
getr regs 11 = (Z_to_bv 64 731416) ->
getr regs 18 = (Z_to_bv 64 599432) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 421740) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 599632) ->
getr regs' 8 = (pn_w sp0 av ev) ->
getr regs' 9 = s1v ->
getr regs' 10 = (Z_to_bv 64 0) ->
getr regs' 11 = (Z_to_bv 64 731416) ->
getr regs' 12 = (Z_to_bv 64 599552) ->
getr regs' 18 = (Z_to_bv 64 731360) ->
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
G (mkst regs' (0x66f6c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x674b4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_674b4 D_674b4.
stw F_674b8 D_674b8 (Z_to_bv 64 599464) tid ltac:(ok_data).
stw F_674bc D_674bc (Z_to_bv 64 599584) (Z_to_bv 64 731416) ltac:(ok_data).
stw F_674c0 D_674c0 (Z_to_bv 64 599552) (Z_to_bv 64 599552) ltac:(ok_data).
sn F_674c4 D_674c4.
ld_step F_674c8 D_674c8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b28c8_8) ltac:(apply bytes_le_to_Z_8).
stw F_674cc D_674cc (Z_to_bv 64 599440) (Z_to_bv 64 599432) ltac:(ok_data).
stw F_674d0 D_674d0 (Z_to_bv 64 599448) (Z_to_bv 64 599432) ltac:(ok_data).
stw F_674d4 D_674d4 (Z_to_bv 64 599456) (Z_to_bv 64 0) ltac:(ok_data).
sn F_674d8 D_674d8.
ld_step F_674e0 D_674e0 (word_to_le_bytes 8 (Z_to_bv 64 421740)) (Z_to_bv 64 421740) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_674e4 D_674e4 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_674e8 D_674e8 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_674ec D_674ec (word_to_le_bytes 8 (Z_to_bv 64 731360)) (Z_to_bv 64 731360) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_674f0 D_674f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_674f4 D_674f4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_674f8 D_674f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_674fc D_674fc (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_67500 D_67500 (0x66f6c : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

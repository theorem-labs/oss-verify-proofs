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
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import StartupTac ArgvEnv RefLayout UbImg UbStartupDefs Ub_code_2b52bc_2b5e0c Ub_code_2c43e8_2c43f4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
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
getr regs 1 = Z_to_bv 64 2839576 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 3498792 ->
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
getr regs' 9 = (Z_to_bv 64 3498792) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 3498144) ->
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
G (mkst regs' (0x2b5788 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x2b5700 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_2b56b8 D_2b56b8 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
stw F_2b56bc D_2b56bc (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 2839576) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_2b56c0 D_2b56c0 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_2b56c4 D_2b56c4 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_2b56c8 D_2b56c8 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 3498792) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_2b56cc D_2b56cc (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_2b56d0 D_2b56d0 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_2b56d4 D_2b56d4 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
ld_step F_2b56d8 D_2b56d8 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_2b56dc D_2b56dc.  (* [comment removed for export] *)
sn F_2b56e0 D_2b56e0.  (* [comment removed for export] *)
sn F_2b56e4 D_2b56e4.  (* [comment removed for export] *)
sn F_2b56e8 D_2b56e8.  (* [comment removed for export] *)
stepb_ft F_2b56ec D_2b56ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b56f0 D_2b56f0.  (* [comment removed for export] *)
sn F_2b56f4 D_2b56f4.  (* [comment removed for export] *)
sn F_2b56f8 D_2b56f8.  (* [comment removed for export] *)
ld_step F_2b56fc D_2b56fc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b5700 D_2b5700 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_2b5704 D_2b5704.  (* [comment removed for export] *)
sn F_2b5708 D_2b5708.  (* [comment removed for export] *)
ld_step F_2b570c D_2b570c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_323470_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
ld_step F_2b5710 D_2b5710 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_321570_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_2b5714 D_2b5714.  (* [comment removed for export] *)
sn F_2b5718 D_2b5718.  (* [comment removed for export] *)
sn F_2b571c D_2b571c.  (* [comment removed for export] *)
sn F_2b5720 D_2b5720.  (* [comment removed for export] *)
sn F_2b5724 D_2b5724.  (* [comment removed for export] *)
sn F_2b5728 D_2b5728.  (* [comment removed for export] *)
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
getr regs 9 = Z_to_bv 64 3498792 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 3498144 ->
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
getr regs' 9 = (Z_to_bv 64 3498792) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 3498144) ->
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
G (mkst regs' (0x2b5788 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x2b5788 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_tk F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b572c D_2b572c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_2b5730 D_2b5730.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
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
getr regs 9 = Z_to_bv 64 3498792 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 3498144 ->
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
getr regs' 9 = (Z_to_bv 64 3498792) ->
getr regs' 11 = (Z_to_bv 64 3498144) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x2b57d8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x2b5788 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_ft F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b576c D_2b576c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
stepb_tk F_2b5770 D_2b5770 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_ft F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b5740 D_2b5740 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_2b5744 D_2b5744 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_2b5748 D_2b5748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b575c D_2b575c.  (* [comment removed for export] *)
stepb_ft F_2b5760 D_2b5760 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5764 D_2b5764.  (* [comment removed for export] *)
stepb_tk F_2b5768 D_2b5768 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5788 D_2b5788.  (* [comment removed for export] *)
sn F_2b578c D_2b578c.  (* [comment removed for export] *)
sn F_2b5734 D_2b5734.  (* [comment removed for export] *)
sn F_2b5738 D_2b5738.  (* [comment removed for export] *)
stepb_tk F_2b573c D_2b573c ltac:(pin; cond_compute).  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 3498792 ->
getr regs 11 = Z_to_bv 64 3498144 ->
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
getr regs' 4 = (Z_to_bv 64 3367064) ->
getr regs' 8 = (Z_to_bv 64 3367064) ->
getr regs' 10 = (Z_to_bv 64 3498144) ->
getr regs' 11 = (Z_to_bv 64 3498848) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 3366856) ->
getr regs' 15 = (Z_to_bv 64 18446744073706184552) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 3366864) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 3367080) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x2b595c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x2b57d8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_2b5790 D_2b5790 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_2b57c8 D_2b57c8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_335fa0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b57cc D_2b57cc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_335fb0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b57d0 D_2b57d0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_335fb8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_2b57d4 D_2b57d4.  (* [comment removed for export] *)
sn F_2b57d8 D_2b57d8.  (* [comment removed for export] *)
sn F_2b57dc D_2b57dc.  (* [comment removed for export] *)
sn F_2b57e0 D_2b57e0.  (* [comment removed for export] *)
sn F_2b57e4 D_2b57e4.  (* [comment removed for export] *)
sn F_2b57e8 D_2b57e8.  (* [comment removed for export] *)
sn F_2b57ec D_2b57ec.  (* [comment removed for export] *)
stw F_2b57f0 D_2b57f0 (Z_to_bv 64 0x3560c0) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b57f4 D_2b57f4 (Z_to_bv 64 0x3560d0) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stepb_ft F_2b57f8 D_2b57f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b57fc D_2b57fc.  (* [comment removed for export] *)
stw F_2b5800 D_2b5800 (Z_to_bv 64 0x3560c8) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
sn F_2b5804 D_2b5804.  (* [comment removed for export] *)
sn F_2b5808 D_2b5808.  (* [comment removed for export] *)
sn F_2b580c D_2b580c.  (* [comment removed for export] *)
sn F_2b5810 D_2b5810.  (* [comment removed for export] *)
sn F_2b5814 D_2b5814.  (* [comment removed for export] *)
sn F_2b5818 D_2b5818.
stw F_2b581c D_2b581c (Z_to_bv 64 0x356340) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b5820 D_2b5820 (Z_to_bv 64 0x356348) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
stepb_tk F_2b5824 D_2b5824 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b5858 D_2b5858.  (* [comment removed for export] *)
ld_step F_2b585c D_2b585c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_336378_8) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      (* [comment removed for export] *)
ld_step F_2b5860 D_2b5860 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_336390_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_2b5864 D_2b5864.
      (* [comment removed for export] *)
sn F_2b5868 D_2b5868.  (* [comment removed for export] *)
sn F_2b586c D_2b586c.  (* [comment removed for export] *)
sn F_2b5870 D_2b5870.  (* [comment removed for export] *)
sn F_2b5874 D_2b5874.  (* [comment removed for export] *)
sn F_2b5878 D_2b5878.  (* [comment removed for export] *)
sn F_2b587c D_2b587c.  (* [comment removed for export] *)
sn F_2b5880 D_2b5880.  (* [comment removed for export] *)
sn F_2b5884 D_2b5884.  (* [comment removed for export] *)
sn F_2b5888 D_2b5888.  (* [comment removed for export] *)
sn F_2b588c D_2b588c.  (* [comment removed for export] *)
stepb_tk F_2b5890 D_2b5890 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stw F_2b58d8 D_2b58d8 (Z_to_bv 64 0x3360a8) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b58dc D_2b58dc (Z_to_bv 64 0x336090) (Z_to_bv 64 0x3360a8) ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b58e0 D_2b58e0 (Z_to_bv 64 0x335fd0) (Z_to_bv 64 0x335fd0) ltac:(ok_data).  (* [comment removed for export] *)
sn F_2b58e4 D_2b58e4.  (* [comment removed for export] *)
sn F_2b58e8 D_2b58e8.  (* [comment removed for export] *)
sn F_2c43e8 D_2c43e8.  (* [comment removed for export] *)
sn F_2c43ec D_2c43ec.  (* [comment removed for export] *)
stepret F_2c43f0 D_2c43f0 (0x2b5934 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
stepb_ft F_2b58ec D_2b58ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_ft F_2b58f0 D_2b58f0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_2b58f4 D_2b58f4.  (* [comment removed for export] *)
stw F_2b58f8 D_2b58f8 (Z_to_bv 64 0x356328) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
sn F_2b58fc D_2b58fc.  (* [comment removed for export] *)
sn F_2b5900 D_2b5900.  (* [comment removed for export] *)
stw F_2b5904 D_2b5904 (Z_to_bv 64 0x335ff8) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
sn F_2b5908 D_2b5908.  (* [comment removed for export] *)
sn F_2b590c D_2b590c.  (* [comment removed for export] *)
sn F_2b5910 D_2b5910.  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 3367064 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 3498848 ->
getr regs 18 = Z_to_bv 64 3366864 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 3367064) ->
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
G (mkst regs' (0x2b5418 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x2b5960 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_2b5918 D_2b5918.  (* [comment removed for export] *)
stw F_2b591c D_2b591c (Z_to_bv 64 3366896) tid ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b5920 D_2b5920 (Z_to_bv 64 3367016) (Z_to_bv 64 3498848) ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b5924 D_2b5924 (Z_to_bv 64 3366984) (Z_to_bv 64 3366984) ltac:(ok_data).  (* [comment removed for export] *)
sn F_2b5928 D_2b5928.  (* [comment removed for export] *)
ld_step F_2b592c D_2b592c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_336350_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
stw F_2b5930 D_2b5930 (Z_to_bv 64 3366872) (Z_to_bv 64 3366864) ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b5934 D_2b5934 (Z_to_bv 64 3366880) (Z_to_bv 64 3366864) ltac:(ok_data).  (* [comment removed for export] *)
stw F_2b5938 D_2b5938 (Z_to_bv 64 3366888) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
sn F_2b593c D_2b593c.  (* [comment removed for export] *)
ld_step F_2b5944 D_2b5944 (word_to_le_bytes 8 (Z_to_bv 64 2839576)) (Z_to_bv 64 2839576) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b5948 D_2b5948 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b594c D_2b594c (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b5950 D_2b5950 (word_to_le_bytes 8 (Z_to_bv 64 3498792)) (Z_to_bv 64 3498792) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b5954 D_2b5954 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b5958 D_2b5958 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_2b595c D_2b595c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sv F_2b5960 D_2b5960 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
stepret F_2b5964 D_2b5964 (0x2b5418 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import
  StartupTac ArgvEnv RefLayout StartupRnd U.S0Img U.S0StartupDefs
  U.S0_code_1f188_1f438 U.S0_code_27518_27524.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSt.
Import WalkHideSt.OptIn.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.                  (* [comment removed for export] *)
  Variable hw : word.                   (* [comment removed for export] *)
  Variable rnd : EntryDraw.             (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    cps_destruct (rnd_facts SEGS RPH sp0 av ev uid hw rnd Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 166460 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = (pn_w sp0 av ev) ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 410736 ->
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
getr regs' 9 = (Z_to_bv 64 410736) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 410088) ->
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
G (mkst regs' (0x28cd4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x28c4c : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid. pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_1f188 D_1f188 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
stw F_1f18c D_1f18c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 166460) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_1f190 D_1f190 (Z_to_bv 64 (bv_unsigned sp0 - 432)) ((pn_w sp0 av ev)) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_1f194 D_1f194 (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_1f198 D_1f198 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 410736) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_1f19c D_1f19c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_1f1a0 D_1f1a0 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
stw F_1f1a4 D_1f1a4 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
ld_step F_1f1a8 D_1f1a8 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_1f1ac D_1f1ac.  (* [comment removed for export] *)
sn F_1f1b0 D_1f1b0.  (* [comment removed for export] *)
sn F_1f1b4 D_1f1b4.  (* [comment removed for export] *)
sn F_1f1b8 D_1f1b8.  (* [comment removed for export] *)
stepb_ft F_1f1bc D_1f1bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f1c0 D_1f1c0.  (* [comment removed for export] *)
sn F_1f1c4 D_1f1c4.  (* [comment removed for export] *)
sn F_1f1c8 D_1f1c8.  (* [comment removed for export] *)
ld_step F_1f1cc D_1f1cc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f1d0 D_1f1d0 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_1f1d4 D_1f1d4.  (* [comment removed for export] *)
sn F_1f1d8 D_1f1d8.  (* [comment removed for export] *)
ld_step F_1f1dc D_1f1dc (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_2a588_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
ld_step F_1f1e0 D_1f1e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_285f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_1f1e4 D_1f1e4.  (* [comment removed for export] *)
sn F_1f1e8 D_1f1e8.  (* [comment removed for export] *)
sn F_1f1ec D_1f1ec.  (* [comment removed for export] *)
sn F_1f1f0 D_1f1f0.  (* [comment removed for export] *)
sn F_1f1f4 D_1f1f4.  (* [comment removed for export] *)
sn F_1f1f8 D_1f1f8.  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 410736 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 410088 ->
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
getr regs' 9 = (Z_to_bv 64 410736) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 410088) ->
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
G (mkst regs' (0x28cd4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x28cd4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid. pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_tk F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f1fc D_1f1fc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_1f200 D_1f200.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 410736 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 410088 ->
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
getr regs' 9 = (Z_to_bv 64 410736) ->
getr regs' 11 = (Z_to_bv 64 410088) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x28d24 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x28cd4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid. pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_ft F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f23c D_1f23c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
stepb_tk F_1f240 D_1f240 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_ft F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f210 D_1f210 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
stepb_ft F_1f214 D_1f214 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_tk F_1f218 D_1f218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f22c D_1f22c.  (* [comment removed for export] *)
stepb_ft F_1f230 D_1f230 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f234 D_1f234.  (* [comment removed for export] *)
stepb_tk F_1f238 D_1f238 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f258 D_1f258.  (* [comment removed for export] *)
sn F_1f25c D_1f25c.  (* [comment removed for export] *)
sn F_1f204 D_1f204.  (* [comment removed for export] *)
sn F_1f208 D_1f208.  (* [comment removed for export] *)
stepb_tk F_1f20c D_1f20c ltac:(pin; cond_compute).  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 410736 ->
getr regs 11 = Z_to_bv 64 410088 ->
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
getr regs' 4 = (Z_to_bv 64 279008) ->
getr regs' 10 = (Z_to_bv 64 410088) ->
getr regs' 11 = (Z_to_bv 64 410792) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 278800) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709272608) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 278808) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x28ea8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x28d24 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid. pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_1f260 D_1f260 ltac:(pin; cond_compute).  (* [comment removed for export] *)
ld_step F_1f298 D_1f298 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5a6f8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f29c D_1f29c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5a708_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f2a0 D_1f2a0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5a710_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_1f2a4 D_1f2a4.  (* [comment removed for export] *)
sn F_1f2a8 D_1f2a8.  (* [comment removed for export] *)
sn F_1f2ac D_1f2ac.  (* [comment removed for export] *)
sn F_1f2b0 D_1f2b0.  (* [comment removed for export] *)
sn F_1f2b4 D_1f2b4.  (* [comment removed for export] *)
sn F_1f2b8 D_1f2b8.  (* [comment removed for export] *)
sn F_1f2bc D_1f2bc.  (* [comment removed for export] *)
stw F_1f2c0 D_1f2c0 (Z_to_bv 64 410120) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f2c4 D_1f2c4 (Z_to_bv 64 410136) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stepb_ft F_1f2c8 D_1f2c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f2cc D_1f2cc.  (* [comment removed for export] *)
stw F_1f2d0 D_1f2d0 (Z_to_bv 64 410128) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
sn F_1f2d4 D_1f2d4.  (* [comment removed for export] *)
sn F_1f2d8 D_1f2d8.  (* [comment removed for export] *)
sn F_1f2dc D_1f2dc.  (* [comment removed for export] *)
sn F_1f2e0 D_1f2e0.  (* [comment removed for export] *)
sn F_1f2e4 D_1f2e4.  (* [comment removed for export] *)
sn F_1f2e8 D_1f2e8.  (* [comment removed for export] *)
stw F_1f2ec D_1f2ec (Z_to_bv 64 410760) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f2f0 D_1f2f0 (Z_to_bv 64 410768) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
stepb_tk F_1f2f4 D_1f2f4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f328 D_1f328.  (* [comment removed for export] *)
ld_step F_1f32c D_1f32c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5a980_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f330 D_1f330 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5a998_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sn F_1f334 D_1f334.  (* [comment removed for export] *)
sn F_1f338 D_1f338.  (* [comment removed for export] *)
sn F_1f33c D_1f33c.  (* [comment removed for export] *)
sn F_1f340 D_1f340.  (* [comment removed for export] *)
sn F_1f344 D_1f344.  (* [comment removed for export] *)
sn F_1f348 D_1f348.  (* [comment removed for export] *)
sn F_1f34c D_1f34c.  (* [comment removed for export] *)
sn F_1f350 D_1f350.  (* [comment removed for export] *)
sn F_1f354 D_1f354.  (* [comment removed for export] *)
sn F_1f358 D_1f358.  (* [comment removed for export] *)
sn F_1f35c D_1f35c.  (* [comment removed for export] *)
stepb_tk F_1f360 D_1f360 ltac:(pin; cond_compute).  (* [comment removed for export] *)
stw F_1f3a8 D_1f3a8 (Z_to_bv 64 279024) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f3ac D_1f3ac (Z_to_bv 64 279000) (Z_to_bv 64 279024) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f3b0 D_1f3b0 (Z_to_bv 64 278808) (Z_to_bv 64 278808) ltac:(ok_data).  (* [comment removed for export] *)
sn F_1f3b4 D_1f3b4.  (* [comment removed for export] *)
sn F_1f3b8 D_1f3b8.  (* [comment removed for export] *)
sn F_27518 D_27518.  (* [comment removed for export] *)
sn F_2751c D_2751c.  (* [comment removed for export] *)
stepret F_27520 D_27520 (0x28e80 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
stepb_ft F_1f3bc D_1f3bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
stepb_ft F_1f3c0 D_1f3c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
sn F_1f3c4 D_1f3c4.  (* [comment removed for export] *)
stw F_1f3c8 D_1f3c8 (Z_to_bv 64 410736) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
sn F_1f3cc D_1f3cc.  (* [comment removed for export] *)
sn F_1f3d0 D_1f3d0.  (* [comment removed for export] *)
stw F_1f3d4 D_1f3d4 (Z_to_bv 64 278848) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
sn F_1f3d8 D_1f3d8.  (* [comment removed for export] *)
sn F_1f3dc D_1f3dc.  (* [comment removed for export] *)
sn F_1f3e0 D_1f3e0.  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 279008 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 410792 ->
getr regs 18 = Z_to_bv 64 278808 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 279008) ->
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
G (mkst regs' (0x28a3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x28eac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid. pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_1f3e8 D_1f3e8.  (* [comment removed for export] *)
stw F_1f3ec D_1f3ec (Z_to_bv 64 278840) (tid) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f3f0 D_1f3f0 (Z_to_bv 64 278960) (Z_to_bv 64 410792) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f3f4 D_1f3f4 (Z_to_bv 64 278928) (Z_to_bv 64 278928) ltac:(ok_data).  (* [comment removed for export] *)
sn F_1f3f8 D_1f3f8.  (* [comment removed for export] *)
ld_step F_1f3fc D_1f3fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5a958_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
stw F_1f400 D_1f400 (Z_to_bv 64 278816) (Z_to_bv 64 278808) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f404 D_1f404 (Z_to_bv 64 278824) (Z_to_bv 64 278808) ltac:(ok_data).  (* [comment removed for export] *)
stw F_1f408 D_1f408 (Z_to_bv 64 278832) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
sn F_1f40c D_1f40c.  (* [comment removed for export] *)
ld_step F_1f414 D_1f414 (word_to_le_bytes 8 (Z_to_bv 64 166460)) (Z_to_bv 64 166460) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f418 D_1f418 (word_to_le_bytes 8 ((pn_w sp0 av ev))) ((pn_w sp0 av ev)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f41c D_1f41c (word_to_le_bytes 8 (s1v)) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f420 D_1f420 (word_to_le_bytes 8 (Z_to_bv 64 410736)) (Z_to_bv 64 410736) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f424 D_1f424 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f428 D_1f428 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
ld_step F_1f42c D_1f42c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
sv F_1f430 D_1f430 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
stepret F_1f434 D_1f434 (0x28a3c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

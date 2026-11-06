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

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefImg RefStartupDefs Ub_code_dd254_dddf4 Ub_code_f0d00_f0d5c.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~37Corelib4Init9Datatypesr64cons46Stdlib6ZArith6BinInt1Zt53subhfbbv_unsigned~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~r66option~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutjp89EntryDrawt52le" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable Jb : ltac2:(zQ "30!h9!jc!is1>0@1$1@1$0#k0@1$2@1$1@1$0#8").   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : ltac2:(zQ "10!jsc$0").
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : ltac2:(zQ "30!h9!jt9!v3@2$1+nvvvogggggg0@2$2@1$0#k0?3sp0").
  Hypothesis Hhi : ltac2:(zQ "30!h9!jt9!v3@2$1@2$2@1$0#k0?3sp0+ogggggggggg0").
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd)) (only parsing).

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 906088 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 1240712 ->
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
getr regs' 9 = (Z_to_bv 64 1240712) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 1240064) ->
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
G (mkst regs' (0xdd600 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xdd578 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_dd578 D_dd578 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_dd57c D_dd57c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 906088) ltac:(ok_win HJ).
stw F_dd580 D_dd580 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_dd584 D_dd584 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_dd588 D_dd588 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 1240712) ltac:(ok_win HJ).
stw F_dd58c D_dd58c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_dd590 D_dd590 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_dd594 D_dd594 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_dd598 D_dd598 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_dd59c D_dd59c.
sn F_dd5a0 D_dd5a0.
sn F_dd5a4 D_dd5a4.
sn F_dd5a8 D_dd5a8.
stepb_ft F_dd5ac D_dd5ac ltac:(pin; cond_compute).
sn F_dd5b0 D_dd5b0.
sn F_dd5b4 D_dd5b4.
sn F_dd5b8 D_dd5b8.
ld_step F_dd5bc D_dd5bc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd5c0 D_dd5c0 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_dd5c4 D_dd5c4.
sn F_dd5c8 D_dd5c8.
ld_step F_dd5cc D_dd5cc (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_fd0c8_4) ltac:(vm_compute; reflexivity).
ld_step F_dd5d0 D_dd5d0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_fbb20_8) ltac:(apply bytes_le_to_Z_8).
sn F_dd5d4 D_dd5d4.
sn F_dd5d8 D_dd5d8.
sn F_dd5dc D_dd5dc.
sn F_dd5e0 D_dd5e0.
sn F_dd5e4 D_dd5e4.
sn F_dd5e8 D_dd5e8.
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
getr regs 9 = Z_to_bv 64 1240712 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 1240064 ->
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
getr regs' 9 = (Z_to_bv 64 1240712) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 1240064) ->
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
G (mkst regs' (0xdd600 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xdd600 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_dd604 D_dd604 ltac:(pin; cond_compute).
ld_step F_dd5ec D_dd5ec (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_dd5f0 D_dd5f0.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 1240712 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 1240064 ->
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
getr regs' 9 = (Z_to_bv 64 1240712) ->
getr regs' 11 = (Z_to_bv 64 1240064) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0xdd650 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xdd600 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_ft F_dd628 D_dd628 ltac:(pin; cond_compute).
ld_step F_dd62c D_dd62c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_dd630 D_dd630 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_ft F_dd5fc D_dd5fc ltac:(pin; cond_compute).
ld_step F_dd600 D_dd600 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_dd604 D_dd604 ltac:(pin; cond_compute).
stepb_tk F_dd608 D_dd608 ltac:(pin; cond_compute).
sn F_dd61c D_dd61c.
stepb_ft F_dd620 D_dd620 ltac:(pin; cond_compute).
sn F_dd624 D_dd624.
stepb_tk F_dd628 D_dd628 ltac:(pin; cond_compute).
sn F_dd648 D_dd648.
sn F_dd64c D_dd64c.
sn F_dd5f4 D_dd5f4.
sn F_dd5f8 D_dd5f8.
stepb_tk F_dd5fc D_dd5fc ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 1240712 ->
getr regs 11 = Z_to_bv 64 1240064 ->
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
getr regs' 4 = (Z_to_bv 64 1108984) ->
getr regs' 8 = (Z_to_bv 64 1108984) ->
getr regs' 10 = (Z_to_bv 64 1240064) ->
getr regs' 11 = (Z_to_bv 64 1240768) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 1108776) ->
getr regs' 15 = (Z_to_bv 64 18446744073708442632) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 1108784) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 1109000) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0xdd7d4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) ([Z_to_bv 8 1])) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0xdd650 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_dd650 D_dd650 ltac:(pin; cond_compute).
ld_step F_dd688 D_dd688 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12ec10_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd68c D_dd68c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12ec20_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd690 D_dd690 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12ec28_8) ltac:(apply bytes_le_to_Z_8).
sn F_dd694 D_dd694.
sn F_dd698 D_dd698.
sn F_dd69c D_dd69c.
sn F_dd6a0 D_dd6a0.
sn F_dd6a4 D_dd6a4.
sn F_dd6a8 D_dd6a8.
sn F_dd6ac D_dd6ac.
stw F_dd6b0 D_dd6b0 (Z_to_bv 64 0x12ec20) (Z_to_bv 64 0) ltac:(ok_data).
stw F_dd6b4 D_dd6b4 (Z_to_bv 64 0x12ec30) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_dd6b8 D_dd6b8 ltac:(pin; cond_compute).
sn F_dd6bc D_dd6bc.
stw F_dd6c0 D_dd6c0 (Z_to_bv 64 0x12ec28) (Z_to_bv 64 8) ltac:(ok_data).
sn F_dd6c4 D_dd6c4.
sn F_dd6c8 D_dd6c8.
sn F_dd6cc D_dd6cc.
sn F_dd6d0 D_dd6d0.
sn F_dd6d4 D_dd6d4.
sn F_dd6d8 D_dd6d8.
stw F_dd6dc D_dd6dc (Z_to_bv 64 0x12eea0) (Z_to_bv 64 224) ltac:(ok_data).
stw F_dd6e0 D_dd6e0 (Z_to_bv 64 0x12eea8) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_dd6e4 D_dd6e4 ltac:(pin; cond_compute).
sn F_dd718 D_dd718.
ld_step F_dd71c D_dd71c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12ee98_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd720 D_dd720 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12eeb0_8) ltac:(apply bytes_le_to_Z_8).
sn F_dd724 D_dd724.
sn F_dd728 D_dd728.
sn F_dd72c D_dd72c.
sn F_dd730 D_dd730.
sn F_dd734 D_dd734.
sn F_dd738 D_dd738.
sn F_dd73c D_dd73c.
sn F_dd740 D_dd740.
sn F_dd744 D_dd744.
sn F_dd748 D_dd748.
sn F_dd74c D_dd74c.
stepb_tk F_dd750 D_dd750 ltac:(pin; cond_compute).
stw F_dd798 D_dd798 (Z_to_bv 64 0x10ec08) (Z_to_bv 64 0) ltac:(ok_data).
stw F_dd79c D_dd79c (Z_to_bv 64 0x10ebf0) (Z_to_bv 64 0x10ec08) ltac:(ok_data).
stw F_dd7a0 D_dd7a0 (Z_to_bv 64 0x10eb30) (Z_to_bv 64 0x10eb30) ltac:(ok_data).
sn F_dd7a4 D_dd7a4.
sn F_dd7a8 D_dd7a8.
sn F_f0d00 D_f0d00.
sn F_f0d04 D_f0d04.
stepret F_f0d08 D_f0d08 (0xdd7ac : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_dd7ac D_dd7ac ltac:(pin; cond_compute).
stepb_ft F_dd7b0 D_dd7b0 ltac:(pin; cond_compute).
sn F_dd7b4 D_dd7b4.
stw F_dd7b8 D_dd7b8 (Z_to_bv 64 0x12ee88) (Z_to_bv 64 1) ltac:(ok_data).
sn F_dd7bc D_dd7bc.
sn F_dd7c0 D_dd7c0.
stw F_dd7c4 D_dd7c4 (Z_to_bv 64 0x10eb58) (Z_to_bv 64 2) ltac:(ok_data).
sn F_dd7c8 D_dd7c8.
sn F_dd7cc D_dd7cc.
sn F_dd7d0 D_dd7d0.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 1108984 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 1240768 ->
getr regs 18 = Z_to_bv 64 1108784 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 1108984) ->
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
G (mkst regs' (0xdd368 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) ([Z_to_bv 8 1])) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0xdd7d8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) ([Z_to_bv 8 1])) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_dd7d8 D_dd7d8.
stw F_dd7dc D_dd7dc (Z_to_bv 64 1108816) tid ltac:(ok_data).
stw F_dd7e0 D_dd7e0 (Z_to_bv 64 1108936) (Z_to_bv 64 1240768) ltac:(ok_data).
stw F_dd7e4 D_dd7e4 (Z_to_bv 64 1108904) (Z_to_bv 64 1108904) ltac:(ok_data).
sn F_dd7e8 D_dd7e8.
ld_step F_dd7ec D_dd7ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12ee70_8) ltac:(apply bytes_le_to_Z_8).
stw F_dd7f0 D_dd7f0 (Z_to_bv 64 1108792) (Z_to_bv 64 1108784) ltac:(ok_data).
stw F_dd7f4 D_dd7f4 (Z_to_bv 64 1108800) (Z_to_bv 64 1108784) ltac:(ok_data).
stw F_dd7f8 D_dd7f8 (Z_to_bv 64 1108808) (Z_to_bv 64 0) ltac:(ok_data).
sn F_dd7fc D_dd7fc.
ld_step F_dd804 D_dd804 (word_to_le_bytes 8 (Z_to_bv 64 906088)) (Z_to_bv 64 906088) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd808 D_dd808 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd80c D_dd80c (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd810 D_dd810 (word_to_le_bytes 8 (Z_to_bv 64 1240712)) (Z_to_bv 64 1240712) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd814 D_dd814 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd818 D_dd818 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_dd81c D_dd81c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_dd820 D_dd820 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_dd824 D_dd824 (0xdd368 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

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

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs Ref_code_d9dac_da94c Ref_code_ed858_ed8b4        .
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~37Corelib4Init9Datatypesr64cons46Stdlib6ZArith6BinInt1Zt53subhfbbv_unsigned~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~r66option~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutjp69EntryDrawt52le" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable Jb : ltac2:(zQ "30!h9!jc!irf>0@1$1@1$0#k0@1$2@1$1@1$0#8").   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : ltac2:(zQ "10!jsa$0").
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : ltac2:(zQ "30!h9!jt7!v3@2$1+nvvvogggggg0@2$2@1$0#k0?3sp0").
  Hypothesis Hhi : ltac2:(zQ "30!h9!jt7!v3@2$1@2$2@1$0#k0?3sp0+ogggggggggg0").
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd)) (only parsing).

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 892608 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 1227080 ->
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
getr regs' 9 = (Z_to_bv 64 1227080) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 1226432) ->
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
G (mkst regs' (0xda158 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xda0d0 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_da0d0 D_da0d0 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_da0d4 D_da0d4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 892608) ltac:(ok_win HJ).
stw F_da0d8 D_da0d8 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_da0dc D_da0dc (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_da0e0 D_da0e0 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 1227080) ltac:(ok_win HJ).
stw F_da0e4 D_da0e4 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_da0e8 D_da0e8 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_da0ec D_da0ec (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_da0f0 D_da0f0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_da0f4 D_da0f4.
sn F_da0f8 D_da0f8.
sn F_da0fc D_da0fc.
sn F_da100 D_da100.
stepb_ft F_da104 D_da104 ltac:(pin; cond_compute).
sn F_da108 D_da108.
sn F_da10c D_da10c.
sn F_da110 D_da110.
ld_step F_da114 D_da114 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da118 D_da118 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_da11c D_da11c.
sn F_da120 D_da120.
ld_step F_da124 D_da124 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_f9b88_4) ltac:(vm_compute; reflexivity).
ld_step F_da128 D_da128 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f8618_8) ltac:(apply bytes_le_to_Z_8).
sn F_da12c D_da12c.
sn F_da130 D_da130.
sn F_da134 D_da134.
sn F_da138 D_da138.
sn F_da13c D_da13c.
sn F_da140 D_da140.
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
getr regs 9 = Z_to_bv 64 1227080 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 1226432 ->
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
getr regs' 9 = (Z_to_bv 64 1227080) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 1226432) ->
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
G (mkst regs' (0xda158 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xda158 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_da15c D_da15c ltac:(pin; cond_compute).
ld_step F_da144 D_da144 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_da148 D_da148.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 1227080 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 1226432 ->
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
getr regs' 9 = (Z_to_bv 64 1227080) ->
getr regs' 11 = (Z_to_bv 64 1226432) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0xda1a8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xda158 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_ft F_da180 D_da180 ltac:(pin; cond_compute).
ld_step F_da184 D_da184 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_da188 D_da188 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_ft F_da154 D_da154 ltac:(pin; cond_compute).
ld_step F_da158 D_da158 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_da15c D_da15c ltac:(pin; cond_compute).
stepb_tk F_da160 D_da160 ltac:(pin; cond_compute).
sn F_da174 D_da174.
stepb_ft F_da178 D_da178 ltac:(pin; cond_compute).
sn F_da17c D_da17c.
stepb_tk F_da180 D_da180 ltac:(pin; cond_compute).
sn F_da1a0 D_da1a0.
sn F_da1a4 D_da1a4.
sn F_da14c D_da14c.
sn F_da150 D_da150.
stepb_tk F_da154 D_da154 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 1227080 ->
getr regs 11 = Z_to_bv 64 1226432 ->
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
getr regs' 4 = (Z_to_bv 64 1095352) ->
getr regs' 8 = (Z_to_bv 64 1095352) ->
getr regs' 10 = (Z_to_bv 64 1226432) ->
getr regs' 11 = (Z_to_bv 64 1227136) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 1095144) ->
getr regs' 15 = (Z_to_bv 64 18446744073708456264) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 1095152) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 1095368) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0xda32c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) ([Z_to_bv 8 1])) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0xda1a8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_da1a8 D_da1a8 ltac:(pin; cond_compute).
ld_step F_da1e0 D_da1e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12b6d0_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da1e4 D_da1e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12b6e0_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da1e8 D_da1e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12b6e8_8) ltac:(apply bytes_le_to_Z_8).
sn F_da1ec D_da1ec.
sn F_da1f0 D_da1f0.
sn F_da1f4 D_da1f4.
sn F_da1f8 D_da1f8.
sn F_da1fc D_da1fc.
sn F_da200 D_da200.
sn F_da204 D_da204.
stw F_da208 D_da208 (Z_to_bv 64 0x12b6e0) (Z_to_bv 64 0) ltac:(ok_data).
stw F_da20c D_da20c (Z_to_bv 64 0x12b6f0) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_da210 D_da210 ltac:(pin; cond_compute).
sn F_da214 D_da214.
stw F_da218 D_da218 (Z_to_bv 64 0x12b6e8) (Z_to_bv 64 8) ltac:(ok_data).
sn F_da21c D_da21c.
sn F_da220 D_da220.
sn F_da224 D_da224.
sn F_da228 D_da228.
sn F_da22c D_da22c.
sn F_da230 D_da230.
stw F_da234 D_da234 (Z_to_bv 64 0x12b960) (Z_to_bv 64 224) ltac:(ok_data).
stw F_da238 D_da238 (Z_to_bv 64 0x12b968) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_da23c D_da23c ltac:(pin; cond_compute).
sn F_da270 D_da270.
ld_step F_da274 D_da274 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12b958_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da278 D_da278 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12b970_8) ltac:(apply bytes_le_to_Z_8).
sn F_da27c D_da27c.
sn F_da280 D_da280.
sn F_da284 D_da284.
sn F_da288 D_da288.
sn F_da28c D_da28c.
sn F_da290 D_da290.
sn F_da294 D_da294.
sn F_da298 D_da298.
sn F_da29c D_da29c.
sn F_da2a0 D_da2a0.
sn F_da2a4 D_da2a4.
stepb_tk F_da2a8 D_da2a8 ltac:(pin; cond_compute).
stw F_da2f0 D_da2f0 (Z_to_bv 64 0x10b6c8) (Z_to_bv 64 0) ltac:(ok_data).
stw F_da2f4 D_da2f4 (Z_to_bv 64 0x10b6b0) (Z_to_bv 64 0x10b6c8) ltac:(ok_data).
stw F_da2f8 D_da2f8 (Z_to_bv 64 0x10b5f0) (Z_to_bv 64 0x10b5f0) ltac:(ok_data).
sn F_da2fc D_da2fc.
sn F_da300 D_da300.
sn F_ed858 D_ed858.
sn F_ed85c D_ed85c.
stepret F_ed860 D_ed860 (0xda304 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_da304 D_da304 ltac:(pin; cond_compute).
stepb_ft F_da308 D_da308 ltac:(pin; cond_compute).
sn F_da30c D_da30c.
stw F_da310 D_da310 (Z_to_bv 64 0x12b948) (Z_to_bv 64 1) ltac:(ok_data).
sn F_da314 D_da314.
sn F_da318 D_da318.
stw F_da31c D_da31c (Z_to_bv 64 0x10b618) (Z_to_bv 64 2) ltac:(ok_data).
sn F_da320 D_da320.
sn F_da324 D_da324.
sn F_da328 D_da328.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 1095352 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 1227136 ->
getr regs 18 = Z_to_bv 64 1095152 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 1095352) ->
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
G (mkst regs' (0xd9ec0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) ([Z_to_bv 8 1])) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0xda330 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) ([Z_to_bv 8 1])) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_da330 D_da330.
stw F_da334 D_da334 (Z_to_bv 64 1095184) tid ltac:(ok_data).
stw F_da338 D_da338 (Z_to_bv 64 1095304) (Z_to_bv 64 1227136) ltac:(ok_data).
stw F_da33c D_da33c (Z_to_bv 64 1095272) (Z_to_bv 64 1095272) ltac:(ok_data).
sn F_da340 D_da340.
ld_step F_da344 D_da344 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_12b930_8) ltac:(apply bytes_le_to_Z_8).
stw F_da348 D_da348 (Z_to_bv 64 1095160) (Z_to_bv 64 1095152) ltac:(ok_data).
stw F_da34c D_da34c (Z_to_bv 64 1095168) (Z_to_bv 64 1095152) ltac:(ok_data).
stw F_da350 D_da350 (Z_to_bv 64 1095176) (Z_to_bv 64 0) ltac:(ok_data).
sn F_da354 D_da354.
ld_step F_da35c D_da35c (word_to_le_bytes 8 (Z_to_bv 64 892608)) (Z_to_bv 64 892608) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da360 D_da360 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da364 D_da364 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da368 D_da368 (word_to_le_bytes 8 (Z_to_bv 64 1227080)) (Z_to_bv 64 1227080) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da36c D_da36c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da370 D_da370 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_da374 D_da374 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_da378 D_da378 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_da37c D_da37c (0xd9ec0 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

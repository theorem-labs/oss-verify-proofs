(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stdio_defs A_code_e3000_e4000  .
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_stdio_write_run1 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_sub"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_add"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_sltu"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_xor"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_and"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_subw"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_defs.sw_file"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_defs.ssp_cells"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "mem_sw1"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_sub_Z : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R1.)(2.R1.R2.))P,(3.R3.(4.+2.+40.))(5.(6.&40.)(7.(8.&40.R4.)(8.&40.R3.))(8.&40.(9.R4.R3.)))")
(* [comment removed for export] *).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

Lemma v_add_Z : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pa,$0.Pl,(6.&40.)P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))(5.(6.&40.)(:.(8.&40.R3.)R2.)(8.&40.(;.R3.(<.&40.R2.))))")
(* [comment removed for export] *).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_wZ : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pb,(6.&40.)Pc,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+40.)))(5.(6.&40.)(:.R3.(8.&40.R2.))(8.&40.(;.(<.&40.R3.)R2.)))")
(* [comment removed for export] *).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_ZZ' : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Px,$0.Py,$0.P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))(5.(6.&40.)(:.(8.&40.R4.)(8.&40.R3.))(8.&40.(;.R4.R3.)))")
(* [comment removed for export] *).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.

Lemma sltu0_xor_ne : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(=.(5.$0.R4.R3.))(5.(6.&40.)(>.(8.&40.=)(?.(8.&40.R5.)(8.&40.R4.)))(8.&40.+1.))")
(* [comment removed for export] *).
Proof.
  intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
  rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
  pose proof (Z_lxor_range a b Ha Hb) as Hr.
  rewrite u_Z2bv by lia.
  destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
  intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
  rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Lemma sltu_ge : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R1.)(2.R1.R2.))P,(3.R3.(4.+2.+40.))(5.(6.&40.)(>.(8.&40.R4.)(8.&40.R3.))(8.&40.=))")
(* [comment removed for export] *).
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

Lemma sltu_lt : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R2.)(3.R2.R1.))P,(3.R2.(4.+2.+40.))(5.(6.&40.)(>.(8.&40.R4.)(8.&40.R3.))(8.&40.+1.))")
(* [comment removed for export] *).
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
  intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
  destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_m1_l : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pa,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+40.)))(5.(6.&40.)(10.(8.&40.+????????????????.)(8.&40.R2.))(8.&40.R2.))")
(* [comment removed for export] *).
Proof.
  intros a H. unfold v_and. u_norm.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  f_equal. apply Z.mod_small. lia.
Qed.

Lemma v_subw_small_lit : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R1.)(2.R1.R2.))P,(3.R3.(4.+2.+1?.))(5.(6.&40.)(11.(8.&40.R4.)(8.&40.R3.))(8.&40.(9.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros a b H H2. unfold v_subw. u_norm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (can : word) (wb n : Z) (s l : word) := ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.O?.(8.&40.(9.O>.+8.))(13.#8.O=.))(8.&40.(9.O>.+10.))(13.#8.O<.))(8.&40.(9.O>.+18.))(13.#8.O;.))(8.&40.(9.O>.+20.))(13.#8.O:.))(8.&40.(9.O>.+28.))(13.#8.O9.))(8.&40.(9.O>.+30.))(13.#8.O8.))(8.&40.(9.O>.+38.))(13.#8.O7.))(8.&40.(9.O>.+40.))(13.#8.O6.))(8.&40.(9.O>.+48.))(13.#8.O5.))(8.&40.(9.O>.+68.))(13.#8.(8.&40.O4.)))(8.&40.(9.O>.+60.))(13.#8.(8.&40.O3.)))(8.&40.(9.O>.+58.))(13.#8.O2.))(8.&40.(9.O>.+50.))(13.#8.O1.))")
(* [comment removed for export] *).

Lemma sw_enter : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pregs,(14.&5.(6.&40.))Pmem,P,(6.&40.)(15.(6.&8.))Prom,P,(6.&40.)(15.(6.&8.))Psu,$0.Pf,$0.Pwb,$0.Pwp,$0.Pfd,$0.Ps,(6.&40.)Pl,(6.&40.)Pbufp,(6.&40.)Pbufsz,(6.&40.)Pcan,(6.&40.)Pret,(6.&40.)P,(5.(6.&40.)(16.R>.(17.&5.+2.$18.))(8.&40.R;.))P,(5.(6.&40.)(16.R?.(17.&5.+:.$18.))(8.&40.R;.))P,(5.(6.&40.)(16.R10.(17.&5.+;.$18.))R8.)P,(5.(6.&40.)(16.R11.(17.&5.+<.$18.))R8.)P,(5.(6.&40.)(16.R12.(17.&5.+1.$18.))R5.)P,(2.(;.+100000000.+70.)R10.)P,(2.R11.+800000000000.)P,(5.$19.(1:.$1;.R14.(8.&40.(9.R12.+70.))#70.)$1<.)P,(2.+?:360.R12.)P,(2.(;.R13.+>8.)+?;358.)P,(1=.R17.R14.R13.R12.R11.R>.R=.)P,(1>.R18.R=.)P,(1.(3.=R13.)(3.R13.+80000000.))P,(1.(2.=R16.)(3.R16.R15.))P,(3.R16.(4.+2.+40.))P,(3.(;.(9.R17.R18.)(<.&40.R14.))+80000000.)(1?.(14.&5.(6.&40.))Lregs',(14.&5.(6.&40.))(1.(20.$1;.(21.$22.R1?.(17.&40.+>66;8.$18.)R1>.R1=.)(21.$22.R1.(17.&40.+>6740.$18.)(23.R1>.R1<.R12.(16.R1?.(17.&5.+8.$18.))(16.R1?.(17.&5.+9.$18.))(16.R1?.(17.&5.+12.$18.))(16.R1?.(17.&5.+13.$18.))(16.R1?.(17.&5.+14.$18.))(16.R1?.(17.&5.+15.$18.))(16.R1?.(17.&5.+16.$18.))R13.R1:.(9.R19.R1:.)R17.R16.)R1=.))(1.(5.(6.&40.)(16.R1.(17.&5.+11.$18.))(8.&40.+42.))(1.(5.(6.&40.)(16.R1.(17.&5.+:.$18.))(8.&40.R18.))(1.(5.(6.&40.)(16.R1.(17.&5.+;.$18.))(8.&40.(9.R1<.+68.)))(1.(5.(6.&40.)(16.R1.(17.&5.+<.$18.))(8.&40.+2.))(1.(5.(6.&40.)(16.R1.(17.&5.+2.$18.))(8.&40.(9.R1<.+70.)))(1.(5.(6.&40.)(16.R1.(17.&5.+8.$18.))R16.)(1.(5.(6.&40.)(16.R1.(17.&5.+9.$18.))(8.&40.R1;.))(1.(5.(6.&40.)(16.R1.(17.&5.+12.$18.))(8.&40.+2.))(1.(5.(6.&40.)(16.R1.(17.&5.+13.$18.))(8.&40.(9.R1<.+68.)))(1.(5.(6.&40.)(16.R1.(17.&5.+15.$18.))(8.&40.+65<:=0.))(1.(5.(6.&40.)(16.R1.(17.&5.+16.$18.))(8.&40.(;.(9.R19.R1:.)(<.&40.R16.))))(1.(5.(6.&40.)(16.R1.(17.&5.+3.$18.))(16.R1?.(17.&5.+3.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+4.$18.))(16.R1?.(17.&5.+4.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+17.$18.))(16.R1?.(17.&5.+17.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+18.$18.))(16.R1?.(17.&5.+18.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+19.$18.))(16.R1?.(17.&5.+19.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+1:.$18.))(16.R1?.(17.&5.+1:.$18.)))(5.(6.&40.)(16.R1.(17.&5.+1;.$18.))(16.R1?.(17.&5.+1;.$18.))))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f wb wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WBP WPhi SMALL.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_e3308 D_e3308. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_e330c D_e330c (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_e3310 D_e3310 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_e3314 D_e3314 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_e3318 D_e3318 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_e331c D_e331c (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_e3320 D_e3320 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_e3324 D_e3324 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_e3328 D_e3328 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_e332c D_e332c. rewrite Ha2.
    stepn F_e3330 D_e3330. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_e3334 D_e3334.
    stepLD8 F_e3338 D_e3338 (Z_to_bv 64 0x65cad0).
    stepLD8 F_e333c D_e333c can.
    stepST F_e3340 D_e3340 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepLD8 F_e3344 D_e3344 (Z_to_bv 64 wp).
    stepLD8 F_e3348 D_e3348 (Z_to_bv 64 wb).
    (* [comment removed for export] *)
    stepn F_e334c D_e334c. rewrite (v_sub_Z wp wb) by lia.
    stepn F_e3350 D_e3350.
    (* [comment removed for export] *)
    stepST F_e3354 D_e3354 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
    stepST F_e3358 D_e3358 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
    stepST F_e335c D_e335c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_e3360 D_e3360 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_e3364 D_e3364. rewrite (v_add_Z (wp - wb) l) by lia.
    stepn F_e3368 D_e3368. rewrite (sltu0_xor_ne wp wb) by lia.
    (* [comment removed for export] *)
    stepb_ft F_e336c D_e336c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_e3370 D_e3370.
    replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepn F_e3374 D_e3374.
    (* [comment removed for export] *)
    stepLD F_e337c D_e337c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_e3380 D_e3380.
    stepn F_e3384 D_e3384.
    stepn F_e3388 D_e3388.
    stepn F_e338c D_e338c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_enter_eq : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run1 ()) "Pregs,(14.&5.(6.&40.))Pmem,P,(6.&40.)(15.(6.&8.))Prom,P,(6.&40.)(15.(6.&8.))Psu,$0.Pf,$0.Pwp,$0.Pfd,$0.Ps,(6.&40.)Pl,(6.&40.)Pbufp,(6.&40.)Pbufsz,(6.&40.)Pcan,(6.&40.)Pret,(6.&40.)P,(5.(6.&40.)(16.R=.(17.&5.+2.$18.))(8.&40.R:.))P,(5.(6.&40.)(16.R>.(17.&5.+:.$18.))(8.&40.R:.))P,(5.(6.&40.)(16.R?.(17.&5.+;.$18.))R8.)P,(5.(6.&40.)(16.R10.(17.&5.+<.$18.))R8.)P,(5.(6.&40.)(16.R11.(17.&5.+1.$18.))R5.)P,(2.(;.+100000000.+70.)R?.)P,(2.R10.+800000000000.)P,(5.$19.(1:.$1;.R13.(8.&40.(9.R11.+70.))#70.)$1<.)P,(2.+?:360.R11.)P,(2.(;.R12.+>8.)+?;358.)P,(1=.R16.R13.R12.R12.R11.R>.R=.)P,(1>.R17.R=.)P,(1.(3.=R13.)(3.R13.+80000000.))P,(1.(2.=R15.)(3.R15.(4.+2.+40.)))P,(3.(<.&40.R13.)+80000000.)(1?.(14.&5.(6.&40.))Lregs',(14.&5.(6.&40.))(1.(20.$1;.(21.$22.R1=.(17.&40.+>66;8.$18.)R1<.R1;.)(21.$22.R1.(17.&40.+>6740.$18.)(23.R1<.R1:.R11.(16.R1=.(17.&5.+8.$18.))(16.R1=.(17.&5.+9.$18.))(16.R1=.(17.&5.+12.$18.))(16.R1=.(17.&5.+13.$18.))(16.R1=.(17.&5.+14.$18.))(16.R1=.(17.&5.+15.$18.))(16.R1=.(17.&5.+16.$18.))R12.R18.=R16.R15.)R1;.))(1.(5.(6.&40.)(16.R1.(17.&5.+11.$18.))(8.&40.+42.))(1.(5.(6.&40.)(16.R1.(17.&5.+:.$18.))(8.&40.R17.))(1.(5.(6.&40.)(16.R1.(17.&5.+;.$18.))(8.&40.(9.R1:.+58.)))(1.(5.(6.&40.)(16.R1.(17.&5.+<.$18.))(8.&40.+1.))(1.(5.(6.&40.)(16.R1.(17.&5.+2.$18.))(8.&40.(9.R1:.+70.)))(1.(5.(6.&40.)(16.R1.(17.&5.+8.$18.))R15.)(1.(5.(6.&40.)(16.R1.(17.&5.+9.$18.))(8.&40.R19.))(1.(5.(6.&40.)(16.R1.(17.&5.+12.$18.))(8.&40.+1.))(1.(5.(6.&40.)(16.R1.(17.&5.+13.$18.))(8.&40.(9.R1:.+58.)))(1.(5.(6.&40.)(16.R1.(17.&5.+15.$18.))(8.&40.+65<:=0.))(1.(5.(6.&40.)(16.R1.(17.&5.+16.$18.))R15.)(1.(5.(6.&40.)(16.R1.(17.&5.+3.$18.))(16.R1=.(17.&5.+3.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+4.$18.))(16.R1=.(17.&5.+4.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+17.$18.))(16.R1=.(17.&5.+17.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+18.$18.))(16.R1=.(17.&5.+18.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+19.$18.))(16.R1=.(17.&5.+19.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+1:.$18.))(16.R1=.(17.&5.+1:.$18.)))(5.(6.&40.)(16.R1.(17.&5.+1;.$18.))(16.R1=.(17.&5.+1;.$18.))))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WPhi SMALL.
  pose proof (u64_range l) as Hl.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_e3308 D_e3308. rewrite Hsp. sp_renorm.
    stepST F_e330c D_e330c (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_e3310 D_e3310 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_e3314 D_e3314 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_e3318 D_e3318 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_e331c D_e331c (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_e3320 D_e3320 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_e3324 D_e3324 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_e3328 D_e3328 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    stepn F_e332c D_e332c. rewrite Ha2.
    stepn F_e3330 D_e3330. rewrite Ha0.
    stepn F_e3334 D_e3334.
    stepLD8 F_e3338 D_e3338 (Z_to_bv 64 0x65cad0).
    stepLD8 F_e333c D_e333c can.
    stepST F_e3340 D_e3340 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    stepLD8 F_e3344 D_e3344 (Z_to_bv 64 wp).
    stepLD8 F_e3348 D_e3348 (Z_to_bv 64 wp).
    stepn F_e334c D_e334c. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
    stepn F_e3350 D_e3350.
    stepST F_e3354 D_e3354 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
    stepST F_e3358 D_e3358 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
    stepST F_e335c D_e335c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_e3360 D_e3360 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    stepn F_e3364 D_e3364.
    stepn F_e3368 D_e3368. rewrite sltu0_xor_eq.
    (* [comment removed for export] *)
    stepb_tk F_e336c D_e336c ltac:(apply c_eq_refl).
    stepn F_e3378 D_e3378.
    replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepLD F_e337c D_e337c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_e3380 D_e3380.
    stepn F_e3384 D_e3384.
    stepn F_e3388 D_e3388.
    stepn F_e338c D_e338c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

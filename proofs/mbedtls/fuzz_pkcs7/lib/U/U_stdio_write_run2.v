(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_stdio_write_run1 U_code_3c000_3d000 U_code_3e000_3f000.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_write_run2 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "sw_regs_but"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_add"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"; "mem_sw2"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "(0.(1.(2.&40.)(3.O1.(4.&5.+2.$5.))(3.O2.(4.&5.+2.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+8.$5.))(3.O2.(4.&5.+8.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+9.$5.))(3.O2.(4.&5.+9.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+15.$5.))(3.O2.(4.&5.+15.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+3.$5.))(3.O2.(4.&5.+3.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+4.$5.))(3.O2.(4.&5.+4.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+17.$5.))(3.O2.(4.&5.+17.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+18.$5.))(3.O2.(4.&5.+18.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+19.$5.))(3.O2.(4.&5.+19.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+1:.$5.))(3.O2.(4.&5.+1:.$5.)))(1.(2.&40.)(3.O1.(4.&5.+1;.$5.))(3.O2.(4.&5.+1;.$5.)))))))))))))")
(* [comment removed for export] *).

Lemma sw_c1_eq : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.P,(1.(2.&40.)(3.R4.(4.&5.+:.$5.))(9.&40.R1.))P,(1.(2.&40.)(3.R5.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R3.)(;.R3.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R8.(4.&40.+41:<0.$5.)R7.R6.)(?.$10.R1.(4.&40.+41:<8.$5.)R7.R6.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R5.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R8.(4.&5.+13.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R8.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R8.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R8.(4.&5.+16.$5.)))(11.R8.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_3e374 D_3e374.
    stepn F_3c1dc D_3c1dc.
    stepn F_3c1e0 D_3c1e0.
    stepb_tk F_3c1e4 D_3c1e4 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_3c210 D_3c210 (0x41ac4 : word) ltac:(bveq).
    stepb_ft F_3e378 D_3e378 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.Prem,$8.P,(1.(2.&40.)(3.R5.(4.&5.+:.$5.))(9.&40.R2.))P,(1.(2.&40.)(3.R6.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R4.)(;.R4.+80000000.))P,(0.(:.=R4.)(;.R4.(12.+2.+40.)))P,(13.(1.$8.R6.R5.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R;.(4.&40.+41:<0.$5.)R:.R9.)(?.$10.R1.(4.&40.+41;54.$5.)R:.R9.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R8.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R;.(4.&5.+13.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R;.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R;.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R;.(4.&5.+16.$5.)))(11.R;.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_3e374 D_3e374.
    stepn F_3c1dc D_3c1dc.
    stepn F_3c1e0 D_3c1e0.
    stepb_tk F_3c1e4 D_3c1e4 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_3c210 D_3c210 (0x41ac4 : word) ltac:(bveq).
    stepb_tk F_3e378 D_3e378 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.P,(1.(2.&40.)(3.R4.(4.&5.+:.$5.))(9.&40.R1.))P,(1.(2.&40.)(3.R5.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R3.)(;.R3.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R8.(4.&40.+41;48.$5.)R7.R6.)(?.$10.R1.(4.&40.+41:<8.$5.)R7.R6.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R5.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R8.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R8.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R8.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R8.(4.&5.+16.$5.)))(11.R8.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_3e3fc D_3e3fc.
    stepn F_3c1dc D_3c1dc.
    stepn F_3c1e0 D_3c1e0.
    stepb_tk F_3c1e4 D_3c1e4 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_3c210 D_3c210 (0x41b4c : word) ltac:(bveq).
    stepn F_3e400 D_3e400.
    stepb_tk F_3e404 D_3e404 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.Prem,$8.P,(1.(2.&40.)(3.R5.(4.&5.+:.$5.))(9.&40.R2.))P,(1.(2.&40.)(3.R6.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R4.)(;.R4.+80000000.))P,(0.(:.=R4.)(;.R4.(12.+2.+40.)))P,(13.(1.$8.R6.R5.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R;.(4.&40.+41;48.$5.)R:.R9.)(?.$10.R1.(4.&40.+41;54.$5.)R:.R9.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R8.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R;.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R;.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R;.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R;.(4.&5.+16.$5.)))(11.R;.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_3e3fc D_3e3fc.
    stepn F_3c1dc D_3c1dc.
    stepn F_3c1e0 D_3c1e0.
    stepb_tk F_3c1e4 D_3c1e4 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_3c210 D_3c210 (0x41b4c : word) ltac:(bveq).
    stepn F_3e400 D_3e400.
    stepb_ft F_3e404 D_3e404 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_retry_a : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Psu,$8.Pf,$8.Pfd,$8.Pio,$8.Pic,$8.Pcnt,$8.Pn0,$8.Prem,$8.Pb0,(2.&40.)P,(1.(2.&40.)(3.R<.(4.&5.+:.$5.))(9.&40.R4.))P,(1.(2.&40.)(3.R=.(4.&5.+13.$5.))(9.&40.R7.))P,(1.(2.&40.)(3.R>.(4.&5.+12.$5.))(9.&40.R7.))P,(1.(2.&40.)(3.R?.(4.&5.+16.$5.))(9.&40.R5.))P,(1.(2.&40.)(3.R10.(4.&5.+9.$5.))(9.&40.R<.))P,(1.(2.&40.)(3.R11.(4.&5.+2.$5.))(9.&40.(14.R>.+70.)))P,(:.(15.+100000000.+70.)R?.)P,(:.R10.+800000000000.)P,(:.+4<000.R10.)P,(:.(15.R11.+>8.)+7=330.)P,(:.(14.R13.+68.)R10.)P,(:.(15.R11.+10.)(14.R14.+48.))P,(0.(:.+1.R11.)(:.R11.+2.))P,(0.(:.+1.R11.)(:.R11.R10.))P,(;.R11.(12.+2.+3>.))P,(:.R13.R11.)P,(;.R12.(12.+2.+3>.))P,(:.(15.(16.&40.R12.)R14.)(12.+2.+40.))P,(1.$17.(18.$>.R1=.(9.&40.(14.R1;.+70.))#70.)$19.)P,(1.(7.(1:.(2.&8.)))(1;.$>.R1>.(9.&40.R19.)#8.)(1<.(1:.(2.&8.))(1=.#8.R14.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1?.(9.&40.(15.R1:.+8.))#8.)(1<.(1:.(2.&8.))(1=.#8.(9.&40.R17.))))P,(1.(7.(1:.(2.&8.)))(1;.$>.R20.(9.&40.(15.R1=.+78.))#4.)(1<.(1:.(2.&8.))(1=.#4.(9.&40.R1<.))))P,(0.(;.=R1=.)(;.R1=.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R24.(4.&40.+41;54.$5.)R23.R22.)(?.$10.R1.(4.&40.+41;44.$5.)(1>.(1>.R23.(9.&40.R1>.)(1=.#8.(9.&40.(15.(16.&40.R19.)R1<.))))(9.&40.(15.R1>.+8.))(1=.#8.(9.&40.(14.R1;.R1<.))))R22.))(0.(1.(2.&40.)(3.R1.(4.&5.+11.$5.))(9.&40.+42.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R1?.))(0.(1.(2.&40.)(3.R1.(4.&5.+;.$5.))(9.&40.R1>.))(0.(1.(2.&40.)(3.R1.(4.&5.+<.$5.))(9.&40.R1=.))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(9.&40.R1=.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(9.&40.R1>.))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(9.&40.R1>.))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(9.&40.(14.R1:.R1<.)))(11.R24.R1.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f fd io ic cnt n0 rem b0
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
  pose proof (u64_range b0) as Hb0.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_3e408 D_3e408 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_3e40c D_3e40c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_3e410 D_3e410. rewrite Ha0, (sltu_ge n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_3e414 D_3e414.
    stepn F_3e418 D_3e418. rewrite Hs3.
    (* [comment removed for export] *)
    stepLD8 F_3e41c D_3e41c b0.
    (* [comment removed for export] *)
    stepn F_3e420 D_3e420.
    stepn F_3e424 D_3e424. rewrite v_and_0_l.
    stepn F_3e428 D_3e428. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_3e42c D_3e42c. rewrite (v_add_wZ b0 cnt) by lia.
    (* [comment removed for export] *)
    stepST F_3e430 D_3e430 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_tk F_3e434 D_3e434 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    stepn F_3e3cc D_3e3cc.
    stepn F_3e3d0 D_3e3d0.
    stepn F_3e3d4 D_3e3d4. rewrite Hs3, (v_add_ZZ' io 8) by lia.
    (* [comment removed for export] *)
    stepLD8 F_3e3d8 D_3e3d8 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_3e3dc D_3e3dc. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_3e3e0 D_3e3e0 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_3e3e4 D_3e3e4. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_3e3e8 D_3e3e8. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_3e3ec D_3e3ec (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_3e3f0 D_3e3f0.
    stepn F_3e3f4 D_3e3f4.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.


(* [comment removed for export] *)
Lemma sw_retry_b : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Psu,$8.Pf,$8.Pfd,$8.Pio,$8.Pcnt,$8.Pn0,$8.Pn1,$8.Prem,$8.Pb1,(2.&40.)P,(1.(2.&40.)(3.R<.(4.&5.+:.$5.))(9.&40.R5.))P,(1.(2.&40.)(3.R=.(4.&5.+13.$5.))(9.&40.R7.))P,(1.(2.&40.)(3.R>.(4.&5.+12.$5.))(9.&40.+2.))P,(1.(2.&40.)(3.R?.(4.&5.+16.$5.))(9.&40.R5.))P,(1.(2.&40.)(3.R10.(4.&5.+9.$5.))(9.&40.R<.))P,(1.(2.&40.)(3.R11.(4.&5.+2.$5.))(9.&40.(14.R>.+70.)))P,(:.(15.+100000000.+70.)R?.)P,(:.R10.+800000000000.)P,(:.+4<000.R10.)P,(:.(15.R11.+>8.)+7=330.)P,(:.(14.R13.+68.)R10.)P,(:.(15.R11.+20.)(14.R14.+48.))P,(0.(:.=R10.)(;.R10.R11.))P,(:.R12.R?.)P,(;.R10.(12.+2.+3>.))P,(:.(14.R14.R13.)R12.)P,(;.R13.(12.+2.+3>.))P,(:.(15.(16.&40.R12.)R14.)(12.+2.+40.))P,(1.$17.(18.$>.R1=.(9.&40.(14.R1;.+70.))#70.)$19.)P,(1.(7.(1:.(2.&8.)))(1;.$>.R1>.(9.&40.(15.R19.+8.))#8.)(1<.(1:.(2.&8.))(1=.#8.(9.&40.R17.))))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1?.(9.&40.(15.R1:.+10.))#8.)(1<.(1:.(2.&8.))(1=.#8.R15.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R20.(9.&40.(15.R1;.+18.))#8.)(1<.(1:.(2.&8.))(1=.#8.(9.&40.R18.))))P,(1.(7.(1:.(2.&8.)))(1;.$>.R21.(9.&40.(15.R1>.+78.))#4.)(1<.(1:.(2.&8.))(1=.#4.(9.&40.R1=.))))P,(0.(;.=R1>.)(;.R1>.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R25.(4.&40.+41;54.$5.)R24.R23.)(?.$10.R1.(4.&40.+41;44.$5.)(1>.(1>.R24.(9.&40.(15.R1?.+10.))(1=.#8.(9.&40.(15.(16.&40.R1:.)(14.R1>.R1=.)))))(9.&40.(15.R1?.+18.))(1=.#8.(9.&40.(14.R1<.(14.R1>.R1=.)))))R23.))(0.(1.(2.&40.)(3.R1.(4.&5.+11.$5.))(9.&40.+42.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R20.))(0.(1.(2.&40.)(3.R1.(4.&5.+;.$5.))(9.&40.(15.R1?.+10.)))(0.(1.(2.&40.)(3.R1.(4.&5.+<.$5.))(9.&40.+1.))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(9.&40.+1.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(9.&40.R1?.))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(9.&40.(15.R1?.+10.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(9.&40.(14.R1;.R1>.)))(11.R25.R1.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f fd io cnt n0 n1 rem b1
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
  pose proof (u64_range b1) as Hb1.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_3e408 D_3e408 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_3e40c D_3e40c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_3e410 D_3e410. rewrite Ha0, (sltu_lt n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_3e414 D_3e414.
    stepn F_3e418 D_3e418. rewrite Hs3, (v_add_ZZ' io 16) by lia.
    (* [comment removed for export] *)
    stepLD8 F_3e41c D_3e41c b1.
    (* [comment removed for export] *)
    stepn F_3e420 D_3e420.
    stepn F_3e424 D_3e424. rewrite (v_and_m1_l n0) by lia.
    stepn F_3e428 D_3e428. rewrite Ha0, (v_sub_Z cnt n0) by lia.
    (* [comment removed for export] *)
    stepn F_3e42c D_3e42c. rewrite (v_add_wZ b1 (cnt - n0)) by lia.
    (* [comment removed for export] *)
    stepST F_3e430 D_3e430 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_ft F_3e434 D_3e434 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepn F_3e438 D_3e438.
    stepn F_3e43c D_3e43c.
    stepn F_3e3d0 D_3e3d0.
    stepn F_3e3d4 D_3e3d4. rewrite Hs3, (v_add_ZZ' io 24) by lia.
    (* [comment removed for export] *)
    stepLD8 F_3e3d8 D_3e3d8 (Z_to_bv 64 n1).
    (* [comment removed for export] *)
    stepn F_3e3dc D_3e3dc. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_3e3e0 D_3e3e0 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_3e3e4 D_3e3e4. rewrite Hs2. vals_lit.
    (* [comment removed for export] *)
    stepn F_3e3e8 D_3e3e8. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_3e3ec D_3e3ec (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_3e3f0 D_3e3f0.
    stepn F_3e3f4 D_3e3f4.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) := ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "(1>.(1>.(1>.O4.(9.&40.(15.O3.+20.))(1=.#8.(1?.O2.O1.)))(9.&40.(15.O3.+28.))(1=.#8.O2.))(9.&40.(15.O3.+38.))(1=.#8.O2.))")
(* [comment removed for export] *).

Lemma sw_done : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Psu,$8.Pf,$8.Pl,(2.&40.)Pbufp,(2.&40.)Pbufsz,(2.&40.)Pcan,(2.&40.)Pret,(2.&40.)Ps0v,(2.&40.)Ps1v,(2.&40.)Ps2v,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)P,(1.(2.&40.)(3.R11.(4.&5.+2.$5.))(9.&40.(14.R>.+70.)))P,(1.(2.&40.)(3.R12.(4.&5.+8.$5.))R=.)P,(1.(2.&40.)(3.R13.(4.&5.+9.$5.))(9.&40.R?.))P,(1.(2.&40.)(3.R14.(4.&5.+15.$5.))(9.&40.+7=330.))P,(:.(15.+100000000.+70.)R12.)P,(:.R13.+800000000000.)P,(:.+4<000.R13.)P,(:.(15.R14.+>8.)+7=330.)P,(20.R10.)P,(1.(7.(1:.(2.&8.)))(1;.$>.R19.(9.&40.(14.R17.+8.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1:.(9.&40.(14.R18.+10.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1;.(9.&40.(14.R19.+18.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1<.(9.&40.(14.R1:.+20.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1=.(9.&40.(14.R1;.+28.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1>.(9.&40.(14.R1<.+30.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1?.(9.&40.(14.R1=.+38.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R20.(9.&40.(14.R1>.+40.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R21.(9.&40.(14.R1?.+48.))#8.)(1<.(1:.(2.&8.))(1=.#8.R1:.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R22.(9.&40.+7=330.)#8.)(1<.(1:.(2.&8.))(1=.#8.R1;.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R23.(9.&40.(15.R20.+58.))#8.)(1<.(1:.(2.&8.))(1=.#8.R1>.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R24.(9.&40.(15.R21.+60.))#8.)(1<.(1:.(2.&8.))(1=.#8.R1>.)))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R27.(4.&40.+41:<8.$5.)R26.R25.)(?.$10.R1.R1>.(21.R26.R23.R21.R20.)R25.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))R22.)(0.(1.(2.&40.)(3.R1.(4.&5.+2.$5.))(9.&40.R24.))(0.(1.(2.&40.)(3.R1.(4.&5.+1.$5.))R1>.)(0.(1.(2.&40.)(3.R1.(4.&5.+8.$5.))R1=.)(0.(1.(2.&40.)(3.R1.(4.&5.+9.$5.))R1<.)(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))R1;.)(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))R1:.)(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))R19.)(0.(1.(2.&40.)(3.R1.(4.&5.+15.$5.))R18.)(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))R17.)(0.(1.(2.&40.)(3.R1.(4.&5.+3.$5.))(3.R27.(4.&5.+3.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+4.$5.))(3.R27.(4.&5.+4.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+17.$5.))(3.R27.(4.&5.+17.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+18.$5.))(3.R27.(4.&5.+18.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+19.$5.))(3.R27.(4.&5.+19.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+1:.$5.))(3.R27.(4.&5.+1:.$5.)))(1.(2.&40.)(3.R1.(4.&5.+1;.$5.))(3.R27.(4.&5.+1;.$5.)))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
         Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
         M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
  unfold mem_sw2. eexists. split.
  - (* [comment removed for export] *)
    stepLD F_3e37c D_3e37c (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e380 D_3e380 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_3e384 D_3e384.
    (* [comment removed for export] *)
    stepST F_3e388 D_3e388 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_3e38c D_3e38c (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_3e390 D_3e390 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
    (* [comment removed for export] *)
    stepn F_3e394 D_3e394. rewrite Hs0.
    stepLD F_3e398 D_3e398 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e39c D_3e39c (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_3e3a0 D_3e3a0 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD F_3e3a4 D_3e3a4 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e3a8 D_3e3a8 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e3ac D_3e3ac (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e3b0 D_3e3b0 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e3b4 D_3e3b4 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e3b8 D_3e3b8 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e3bc D_3e3bc (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_3e3c0 D_3e3c0 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_3e3c4 D_3e3c4. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_3e3c8 D_3e3c8 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

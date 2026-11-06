(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface D_iface D_defs FX_Layout FX_Exit FX_Stdio_iface I_iodefs X_xdefs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import HandoffImage.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_HandoffCLX () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3eqbc69OSSVerify5KrLib2K53A02:HandoffCLX9cells_wfbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes3nat00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc69OSSVerify5KrLib2K53A02:HandoffCLX9blist_eqbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00c69OSSVerify5KrLib2K53A02:HandoffCLX8hs_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3lebc69OSSVerify5KrLib2K53A02:HandoffCLX8hs_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG:HandoffKit2mHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leC79OSSVerify5KrLib2K52AS8AsanPlan2AP2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage8klit_cutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP8hs_tableC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02c69OSSVerify5KrLib2K53A02:HandoffCLX<blist_eqb_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53A02<HandoffImage:hi_lit_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX?cells_wfb_soundC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib2K53A02:HandoffCLX;hs_rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage9seg_rw_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX;hi_ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage?seg_rw_ok_soundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A02<HandoffImage9stk_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rK47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib2K53A02:HandoffCLX9hs_out_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX9out_cellsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX7hs_wordC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib2K53A028I_iodefs8OUT_repAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX7hi_blobC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029FX_Layout:file_cellsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC69OSSVerify5KrLib2K54Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX7hs_blobC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX;hi_rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses5mkappC69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX9hs_err_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX9err_cellsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX8err_wendC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX5err_eC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3ltbC69OSSVerify5KrLib2K53A028I_iodefs8ERR_repAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool8orb_propK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib2K52AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega5Tauto4kind02K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib2K53A02:HandoffCLX6hs_gdsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs6gds_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs8gd_cellsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A027X_xdefs5gdesc00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC79OSSVerify5KrLib2K52AS?AxSymExec3Sound4AX2S7u_lit64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX9hs_tid_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage7kw_findC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX6x_tidEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP7fact_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage:kw_find_inC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC79OSSVerify5KrLib2K52AS=AsanPlanSound3APS2MrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS7co_knowC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS=fact_ok_soundC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K52AG:HandoffKit8hk_kwordC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc69OSSVerify5KrLib2K53A02:HandoffCLX;clx_u64_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lC69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2I79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc69OSSVerify5KrLib2K53A02:HandoffCLX:hs_xenv_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX6x_libcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX7x_stdinC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc69OSSVerify5KrLib2K53A02:HandoffCLX7hs_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX8x_atexitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs5XENVAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs:XENV_coreAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs8XENV_trAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027FX_Exit:stdin_fileC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notc69OSSVerify5KrLib2K53A02:HandoffCLX6hi_tidC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX6hi_gdsC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib2K53A027X_xdefs:atx_table1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs:atx_table2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs8asan_gdsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7TR_INCBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7TR_INITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs5ATX_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs;ATX_BUILTINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs8ATX_CALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs6ATX_A0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs8COV_DUMPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX9hs_clx_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage>hi_clx_staticsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX6hi_outC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX6hi_errC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02:HandoffCLX7hi_xenvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Layout<g_read_stageC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hc_fx : PropExec.FPState := PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint cells_wfb (cs : list cell) : bool :=
  match cs with
  | [] => true
  | CB n bs :: r => (Nat.eqb (length bs) n && cells_wfb r)%bool
  | _ :: r => cells_wfb r
  end.

Lemma cells_wfb_sound : forall cs, cells_wfb cs = true -> cells_wf cs.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) [] "p'0h01Hh11ni001nh21vi011vh32csh41mh52H1h62H2h72IHh81bi021bh92bsi032bsh:1ci041ch;1rp;1p;4p;2p;3p;5p10000p4p710p1000Mp4p710p8g000kj1?Tg001Kj12Tg002Ej1CTg002ej15Tg003Jj1=Tg003hj1>Tg004Kj1<Tg005Cj4;Tg005^j18Tg006Vj19Tg007Nj1:Tg008Fj2BTg009>j26Tg009^j27Tg00:>j1ATg00;>j3GTg00;aR0j2@Tg00<<j33Tg00<Vj2FTg00=9j5ETg00=[j3DTg00>;R1f0R2#Ag00>[R333p=1g00?;R4f1R5;D2p=0A3123p=4%?4R3P4%12%25[R1X33%C4#1g00@3R6W0f2R7/05#1P4f3R8,02#1f4R9,05#2]0P8g00@O#5#5#5R:#5#5#5#=#>R;%<2/09#1g00A4f5R<#2P6P9P2O1C;R6%<5/0<#2eW0W2P2O1%82/09#1P6%85/0<#2eW0X2;P2O1%92/09#1P6%95/0<#2eW0X2;P2O1%=:#>R:%:2/09#1P6%:5/0<#2eW0W8P2O1g00APR6%?:1B52f6R;'0#116:5/77R=f7R>#AR?;G2%4=%4?'@P016:7/78#4f8R?#116:8=369f9#2'@P216:9/7<#4f;R<#116:;=36>f<#2P01752#4A3675[R0A36521775#4R;[A3687\;1F52P5n2001000000120000000X46X16P0^46^16P216:>P?P7O3b0P<P2O1C;W6W5P5P2O2n2001000000120000000b01B75/0>#2eW0W9W1P5P2O2n0110400051010110101101011010220100103P2O1W0X71X;3X:4P2DEW3o"). Qed.

Fixpoint blist_eqb (xs ys : list byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (bv_eqb x y && blist_eqb xs' ys')%bool
  | _, _ => false
  end.

Lemma blist_eqb_eq : forall xs ys, blist_eqb xs ys = true -> xs = ys.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) [] "p'0h01Hh12xsh21yh32ysh42H0h52H1h61ah71bi001bh83ys0h92H2h:2IHh;1eh<1xi011lp;1p;3p;2p;6p;5g002ej15Tg003Jj1BTg003hj1;Tg000kR0j1:Tg00<<j30Tg002Ej1<Tg00Aoj29Tg00=[j31Tg00BIj67Tg00Bej26Tg00CDj34Tg00D1j28Tg00;>j3ATg00;aR1j2@Tg00E1j3=Tg000Mj6>Tg00=9j5?Tg00>;R2f1R3f0R4'8g00>[R530p=2A0245p=3g00@O#5#5#5#BR6#;R7#:R8P71234f2R9=083[^38R:X18P0P7%<7R;/24A08;3[P412;;198;W0A1734R<,2;P2g00EfP2p-0P4g00FFR=g00A4n0110000020000X;2g00@3P5P4E7R5P=f3R2=179R>908;/64b4W0X38X27P3P4O2n10110100020020100101X88P0P7f4R0=172R?/24f5R@=170R0=083[P412>;P5P=A080;/64b4W0f7R0f6517/2<f8R<=469R;1803R0;A4%3;%30'@P1f9R0=462#312<9f:=170=08?P4f;R?=46@#312?@P1A4634#3A0793[R1A0734A4693#3R?[A0729\?A=634P3n2001000000120000000X77X67P1^77^67P4f>R1P<P9O3A071<P7f?R6f@R?=176A1740508X27P8P<A17?4A17?0508X18A176<,98P1f=P<P9O2E>P0P4E7b5b0W9W5P3P4O2n2001000000121000000b0W0X38X27P3P4O2n10110100020021100101X88X::X18X<7P4D?W1o"). Qed.

(* [comment removed for export] *)
Definition hs_bytes (ch : acs) (a n : Z) : option (list byte) :=
  match AP.hs_table asegs (klit_cut a (a + n) (kn ch)) a n with Some zs => Some (map (Z_to_bv 8) zs) | None => None end.

(* [comment removed for export] *)
Definition hs_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (cells_wfb cs && Z.leb 0 a && Z.leb (a + Z.of_nat (cells_size cs)) (2 ^ 47)
   && match hs_bytes ch a (Z.of_nat (cells_size cs)) with
      | Some bs => blist_eqb (cells_bytes cs) bs
      | None => false
      end)%bool.

(* [comment removed for export] *)
Definition hs_rw_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (hs_cells ch a cs && seg_rw_ok asegs a (Z.of_nat (cells_size cs)))%bool.

(* [comment removed for export] *)
Definition dec_le (bs : list byte) : Z := fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 bs.
Definition hs_word (ch : acs) (a : Z) (n : nat) : word :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => Z_to_bv 64 (dec_le bs) | None => Z_to_bv 64 0 end.
Definition hs_blob (ch : acs) (a : Z) (n : nat) : list byte :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => bs | None => [] end.
Definition hs_byte (ch : acs) (a : Z) : byte := nth 0 (hs_blob ch a 1) (Z_to_bv 8 0).

Section Cells.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Lemma hi_ro_cells : forall a cs, hs_cells ch a cs = true -> ro_cells asegs m a cs.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Cells"] "p'0h01Hh12Hbh22Hth32Hah43Hhih53Hloh66__sat2h74__x1h81mh91nh:2Hlh;3Hwfh<7__arithh=4__ffh>6__sat1h?8__varmaph@5__withA1ahB2cshC4cstrhD1ehE1li001lhF1oi011ohG2zsi022zsi031bi042bsi051xp;1p;3p;2p;4p;7p;8p;Kp;6g000kj1ATg00Fcj3oTg00:>j15Tg00Gbj23Tg00H@j22Tg002ej1DTg00H]j1KTg00I;j1@Tg00I`j2QTg00J=j26Tg003Jj1nTg003hj1gTg00JZj3GTg00KYj19Tg00D1j2>Tg00;>j3FTg00;aR0j2HTg00LVj3VTg00MNj4=Tg00NGj2<Tg00Ncj2TTg00OCj1STg00P<j3;Tg00Q=j4:Tg00R<R1j1JTg00Aoj2CTg00<<j38Tg00R^j1RTg00SDj4?Tg00S`j2ITg00TBj1BTg00Tdj3PTg00Ugj1LTg00Vcj1MTg00WCj1OTg00Whj2UTg00XPj2NTg00Xlj3mTg00YPj2lTg002Ej1fTg00Z1j2eTg00ZOj1dTg00Zmj1`Tg00[Xj2_Tg00\;j2]Tg00\^j4\Tg00]Ij7[Tg00]mj8^Tg00^Qj2ZTg00_3j2aTg00__j3bTg00`>j4YTg00a0lKcTg00b3j4ETg001Kj1XTg00bkj2WTg000Mj6hTg005Cj4iTg00BIj6jTg00Bej2kTg00>;R2f0R3g00>[R438p=0g00d1R5/63p=4%L3#Mp=11<53p=7g00dOR6g00?;#Ap,2chR7f1R8;o3#0%58f2R9#4'3%18R:,29g00@OR;#DR<#KR=%@<#@#@#@#KR>'QR?'6'3R@P1%D<#D#nR<#gRA#ARBP2AG79:%99/>3g00EfR:n10110500021010400RC;F3%0@%0C'HP0%59f3RC#4'3%19R@,2C/6?'3#0P1PBP2AG7C@%9C/>3P:n10110500021010400#0g00dmR@p,4FULLRDp,5modelREp,2A'RF3VRGf4RHPCC=P3%5Hf5RI#4'3%1H,2I/6?'3#0P1PBP2f6RJ%1I5G7%9J/>3P:n10110500021010400#0%5Jf7RI#4'3RK%1J,2I/6?RJ;F8%0K%0J'HP0%5If8RJ#4'3#0%1I,2J/6?#0P@PGf9RKPJC=P3%5Kf:RL#4'3#0f;RM%1L'2/6?#0%5MRMf<RL#4RN;F8%0M%0N'HP0%5L#0f=RL#4#0P@PGf>RNPLC=P3%5N#0f@RN#4#0P01683#01<98[R01<831698#0RM[1<C9\M1T83P8n2001000000120000000X86X96RMP0^86^96R0P3P5fBROP8O3%7OPMP0P3fDR0fC#1'2RMP?PJO31<M?P@fERM%10R0,2M%S7RJ3;PMP0C:%A6R0#JRO1CO3P@fFRP%1MRM,2P;;JPPPMC:=8O3P1P0P@fHRMfGRQ#1RR,2M;;JPMPRC:=8O3P1PBP2P1P0%JBP8P6PA%R<R<P3C?,IB%BBn10110500021010200fIR1#9RR/>3P:n10110500021010400#0P@PGfJRSP1C=RT]1]2P8P@%1MRM,21=;1JP1PMC:1I0358OP6PAP<P8C?,>R#0%9SRSP6PAP<P9C?RR;P3A8BSRP@p,1Ap,3nx0p,5LIMITp,4SINVp,4argHp,3FS0p,<SEGS_in_hullp,7HULL_okp,9argH_highp,1EP7p,1RPDPEp,2HCPFp,3HA'fLRFfK#LRE#MRD,2FPFPDPCP9PK%OE%7D1U=>1N5=RD%7>1N5?[RE[%7=RKg00A4R7Am=>8UW3%7?\7^3KP8g00ee1l5='CPDeO1PEg00fKRE#f%AE1e68%d6%`6REg00g7RDg00gVR=P=g00h6RKPEPDP=P=PKP61_65g00hV1]6;C\g00i=F[R;%B=P;G^1ZEKP3P91C241a39#0dAb658CYb=b?b@X76%73%78[^76P3fP#1PHO2b<b6b>b6bCPIMKcP@PGPFP6PAP<PCC?CE%XFP@PGfMRC%9FRICE1WFLPBP6PAP<PHC?P@PGfNP3CEXEBP3PIP8EhCiP@PGPCPFC=eb:b1W1W2XG0P3O1P@%1PRP,2Q=;QJPQPPC:%B058OA82:4P2P:P2p-0P3g00FFR:P7n0110300020000XD2g00@3P4P3EjP:1kT3b0W1W2n10110100021110000P3PNO2b2bFb4b0b5b0W5W;P8P3O2n2001000000121000000b0W4W0P8P3O2n2001000000121000000b0W1W0P8P3O2n2001000000121000000b0W0WBWAo"). Qed.

Lemma hi_rw_cells : forall a cs, hs_rw_cells ch a cs = true -> rw_cells asegs m a cs.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Cells"] "h01Hh12Hsh21ah32csp;1p;3p;2p;4p;5g000kj1CTg00i]j3BTg00Fcj33Tg00Ugj11Tg00Vcj12Tg00j_j34Tg00;>j38Tg00;aR0j27Tg00LVj36Tg00kaj45Tg00lZj49Tg00mTj4:Tg00nIj3ATg00H@j2@Tg00oKj4?Tg010@j5<Tg011Hj3=Tg005Cj4>Tg00<<j3;Tg00>;f0R1g00>[3;p=0g00dOg00?;#Cp,2chR2f1R3;B1#0f2R4=323R5g00dmR6%13#2744R7;81%05%07'7P0f3R0=324#0%14#29460#0P6p,4FULLp,5modelp,2A'36R4f4R7P0C5P1f5R0=327#0f6R7%10#2546#0P6P4f7R0P7C9P6P4P0%17#2R2C:R5AA073P6P4P01@02C?P6P0P2P1P4D<5=5C>W1W0P3P1O2n2001000000120000000b0W0W3W2o"). Qed.

End Cells.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition out_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDOUT 4) 0 0 0 F_STDOUT_WRITE RSTDOUT_BUF 1024 1 (hs_word ch (RSTDOUT + 136) 4) 10
    (hs_blob ch (RSTDOUT + 152) 80).
Definition hs_out_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDOUT (out_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDOUT 4)) 72) 0
   && seg_rw_ok asegs RSTDOUT_BUF 1024)%bool.

(* [comment removed for export] *)
Definition err_wend (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 32) 8).
Definition err_e (ch : acs) : Z := bv_unsigned (hs_word ch (RSTDERR + 40) 8).
Definition err_cells (ch : acs) : list cell :=
  file_cells (hs_word ch RSTDERR 4) (err_wend ch) (err_e ch) (err_e ch) F_STDIO_WRITE 0x660550 0 2
    (hs_word ch (RSTDERR + 136) 4) 0xffffffff (hs_blob ch (RSTDERR + 152) 80).
Definition hs_err_ok (ch : acs) : bool :=
  (hs_rw_cells ch RSTDERR (err_cells ch) && Z.eqb (Z.land (bv_unsigned (hs_word ch RSTDERR 4)) 40) 0
   && (Z.eqb (err_wend ch) 0 || (Z.eqb (err_wend ch) 0x660550 && Z.eqb (err_e ch) 0x660550)) && Z.ltb (err_e ch) (2 ^ 63))%bool.

Section Stdio.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation RWC := (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').

(* [comment removed for export] *)
Lemma hi_blob : forall a (n : nat), seg_rw_ok asegs a (Z.of_nat n) = true -> exists bs, rw_cells asegs m a [CB n bs].
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Stdio"] "p'0h02bsh11nh21Hh32H0h42Hbh52Hlh61Sh71Wh81ah92a0h:1eh;1li001xp;1p;3p;5p;4p;2p;6g00Vcj11Tg00j_j3QTg00<<j32Tg00LVj3DTg010@j5PTg00mTj43Tg00H@j29Tg00oKj4;Tg00;aR0j26Tg002ej1:Tg003Jj1CTg003hj1BTg000kj1ATg008Fj25Tg002Ej1@Tg00=[j34Tg00kaj47Tg011cR1j28Tg012=j5OTg009>j2<Tg00lZj4JTg00Ugj1HTg001Kj1>Tg00KYj1GTg013?j1FTg005Cj4=Tg0148j3ITg014Uj2ETg000Mj6?Tg0153j2KTg015Sj1LTg0167j4MTg00b3j4NTg00dmR2f2R3f1R4f0R5CNp=0g00dOg00APR6g00>;%15R79Q24g00>[32P2P3%14R8P5p,4FULLp,5modelp,2A'3DR9DPP2P9P3P8C3P2P9P31938C;'6P0P2P9f3R8%13R3C3P2P9P81983C;g00@O#:#:#:#C#BR3#AR:P2P9f5R;g00?;R<f4R=/55%@<R>34C7X0:'8P5P2P9P;%1=C3P2P9f6R?%1;,9?C;P2P9f7R@P?P5DO1<35R?=26@f8R@=095'6X0:,8:P1P:A26?@f9R@=095'6X0:P2P9f:R115@5=4<>C7X0:,8:P5A26?1f;R?=095'6P01<34=26?f<=094P2P9f>f=R?/55=4<>C7X0:,8:P51<38=26?f?R?=09=P:P2P9fAR=f@R8/55=4<>C7X0:P;P2P9P815?;R0=4<>R<CJP2P9P8%H<#1C3R@%><%G<9098R8%F0%>>P4g00@3C=P:P;A09=5X;:P5%@39I3;1E3;E?P8eC=P6P?P2P9P=P7C3X16P1g016Q,K?%L?E?P@eC=CMW4W5P4P5O2n2001000000121000000W3X0:P4P5O2n2001000000121100000b:W6W7P4P5O2n2001000000121000000b9W2W1W8o"). Qed.

Theorem hi_out : hs_out_ok ch = true -> OUT_repA stdout_init m.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Stdio"] "p'0h01Hh18bufbytesh24tailh31xi001xh42bsh51mh64modeh71nh82Hbh94Hbufh:2Hch;3Hflh<2_Hh=7__arithh>4__ffh?8__varmaph@5__withA1ehB5flagshC1yp;1p;3p;2p;;p;Dp;<p;4p;7g0170j1wTg002ej17Tg0180j1^Tg00i]j3[Tg003Jj1NTg0190j3RTg019nj2WTg00I;j14Tg01:Xj2QTg01;6j2HTg00Gbj2qTg00j_j3iTg00;>j3STg00;aR0j23Tg00LVj3bTg01;Sj2aTg01<Pj3\Tg003hj1PTg000kj1FTg008Fj2OTg002Ej1ETg00=[j3MTg011cR1j2<Tg01=Nj1ZTg00H@j2DTg01>Jj1YTg01?Cj2KTg01@>j1XTg00H]j1JTg01A9j1vTg01B5l;ATg00<<j35Tg009>j2VTg01C5j3ITg01CTj1UTg00NGR2j2?Tg01DOj3uTg01EMlDsTg01FOj2rTg00Aoj2>Tg00VcR3j1GTg01Foj1pTg01GMl<hTg01H2j1gTg00ZOj1fTg00Zmj1eTg00[Xj2TTg00\^j4dTg00]Ij7cTg00^Qj2jTg00_3j2kTg00__j3lTg00`>j4mTg01HPj4nTg005Cj4@Tg0167j4CTg01I;j10Tg00kaj4_Tg01IZl<tTg00>;R4f0R5g00>[R635p=9%75#7p=2%75#4p=B%45#7p=6%45#4p==%75#Jp=8%05#0#0#0p=L%05#0#0#0#0#0#0#0p=`%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=]g00dmR7f2R8f1R9P5C_p=;%45#4#4#4p=:g00APR:g00dOR;P;P;P3P3f3R3P8P9g016QR<g00d1R=P5M<tp=op,2chR>#w#9g00@OR?#7#2#2#B#2#B#6#2#=#2#8R@%^>RA5[>RB%7?RC#7RD#7RE#7#2RF#NRG%L<RH9R>@RI'W%4DRD#2#8RJ'QRK/H=RL'qRM%4?#2#=#2#2#2#6#6#6#=#2#8RN%7F#2#8RF5i7R7;S5%9MRM%97R7'3P0PMP7g01J?ROp,4FULLRPp,5modelRQp,2A'RR3bRS'aRTP5ASBL9%9BRB%9LRL'3P0PBPLPTP5%LH#`#1#1RU#]#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1RVf55\N%NE#PRW#FRXg00?;RY1OV5%EYRZ3M9;SNR[X4XR\'<P1PXP\PTP5%PGR\P3P4P;%ZOR11DNFP=n0100000020000R]P4P;P1%YOR^,K;R_,DNP=n0100000020000R`P4P;P1PNP=n0100000020000RaP4P;%XO%=?#6#2#2#6#6#6#2#6#8Rb%=?#B#:#2#B#6#2#6#8n0100000020000RcPNPF%J?RdP8P4P;%vO%4C#8RC%4?#=#:#:#:#:#:#:#:#Jn0100000020000R?P9M;A9;S@1WG3/QJ=5;=1V;^RJ=IW5%U^RG55X1?_Fg00EfR_9541%F;R1%E;RO75^['3R^'3,3[Re'3'3X1X,<XX2X,<XX6\,<\XB\PIP\PIP]P`PaPcPNPFPdP8P?P9M;A9;S@A5;K=Rf/3eRe'3X1X,<XX2X,<XX6\%4E#2#8,D@=R>HRHPXPIP]P`PaPcPNPFPdPHP?P9M;A9;S@/3eX1X,<XX2X%4D#2#8,D@=u>URUPXPIP]P`PaPcPNPFPdPHP?PUM;A9;S@R?/3eX1XP9PIP=P=P=PbPNPFPdPHPCPUM;A9;S@1OV9=MYZ9;SNRS1V;ORN=IW9%UORZ55XRY1K;O/?FRVA54__R_A51OO[RU'3RC'3RH'3Rd,3fp,1Ap,3nx0p,5LIMITp,4SINVp,4argHp,3FS0p,<SEGS_in_hullp,7HULL_okp,9argH_highp,1EP>p,1RPPPQp,2HCPRp,3HA'P@PAf6RAMDsPfPdP01H95#9A5;89[R0A5;951H89#9Rd[A5;38\d1r95P9n2001000000120000000X5;X7;P0^5;^7;P5PKP=PAO3b0PSPHP5PYPC1>XZPVPU%G<R</?F1?=FRUP;P;P2P5X3;RZP21?95#pXC;X3;P<P=PZPZ%G5,>;X3:1>;=CoPFPF1>;FM<hg00fKR:#E%F:%g;%f;%e;R:g00g7g00gVRZPZg00h6RZP;1T;=g00hV1T;FCdg00i=Fc1j:ZP5P81>461k58#9dAl;=9Cmb>b?b@PUP5b=Cn%GN/?FePVe1>1OX<_C@C@C@C@C@AIWJ9=5XG/3^,3S,3f,3?eCCCCCCCCPTeX8[X4XP9P5O2n2011000000121100000bAX;LX:BP9P5O2n2001000000121000000b0X97X0MP9P5O2n2001000000121000000b0W0o"). Qed.

Theorem hi_err : hs_err_ok ch = true -> ERR_repA m.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Stdio"] "h01Hh12Hwh24tailh32Hah41mh51nh64wendh71eh82Heh94__p1h:6__sat2h;6__sat4h<4__x1h=4__x2h>4modeh?2H1h@2H2hA2HchB3HflhC7__arithhD4__ffhE6__sat1hF6__sat3hG8__varmaphH5__withI5flagsp&0p;1p;3p;2p;Dp;4p;6p;7p;5p;;p;8g01K=k108Tg00H]j16Tg01L=j1rTg00i]j3mTg002ej15Tg003Jj1RTg0190j3ITg019nj2HTg01:Xj2bTg01;6j29Tg00Gbj2ETg01M=j1}Tg01N<j1wTg01O8j2\Tg00I;j13Tg00I`j2XTg01OUj2KTg00;>j3DTg00;aR0j21Tg00LVj3fTg01P2j1eTg003hj1`Tg000kj1VTg01PoR1j2BTg00XPj24Tg011cj27Tg00H@j2JTg01DOk306Tg01EMmD05Tg01FOk204Tg01QIk303Tg01Qek302Tg005Cj4FTg01R?k301Tg01RYj2|Tg01S9j1{Tg00Whj2_Tg00Xlj3^Tg00YPj2xTg00Aoj2WTg002Ej1vTg01H2j1tTg00Z1j2sTg01T6j4qTg00ZOj1pTg00Zmj1oTg00[Xj2NTg00\;j2ZTg00\^j4OTg01TTj6nTg00TBj1lTg01U8j3kTg01U[j7]Tg01V?j7jTg01Vcj5iTg01WGj6uTg00^Qj2hTg00_3j2gTg00__j3yTg00`>j4zTg0167j4ATg00<<j3QTg01I;j10Tg01B5l;~Tg00kak400Tg00NGj2dTg00]Ij7aTg00]mj8cTg00>;R2f0R3g00>[R43Qp=2%53#5p=:%33#5#5#5p=<%33#5p=S%03#0#0#0p=T%53#3p=>%33#3#3#3p=;%33#3p=UP3f1R5f2R6f3R7f4R8f5R9g00d1R:f6f7R;f8R<f9M;~p=?g00dmP6P5P3H00p=@g00dOR=?Q3:p=CAQ=53p==1d:3p=8%03#0#0#0#0#0#0#0p>07%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=GP5g00g7R>g00gVR?P?g00h6R@P3g00i=RAFap=YP6P>P?P?P@P5P3F]p=[P=P5g01WkP3COp=PP5P>P?P?g01XRRBP3PAFap=LP7P>P?P?P@P6P5P3Gcp=Mp,2chRA$08#2g00@ORC#:#:#:#<#<#S#<#6RD%rARE5mARF%5CRG#5RH#5RI#5#:RJ#RRKg016Q#TRL9IADRM'H%<G#6RN'bRO/9:RP'ERQ%}ARR/9:RS%SC#>#<#:#>#>#>#>#:#:#6RT,9RRU%wARV/9TRW'ERX'\RY'ERZ%6GRG%3CR[#;R\#6R]'XR^,KVR_;D3%2ZRZ%2_R_'1P0PZP_p,4FULLR`p,5modelRap,2A'Rb3fRc#eRdP3ADQY5%2QRQ%2YRY'1P0PQPYPdP3ADFP5%2FRF%2PRP'1P0PFPPPdP3%`KRe%RI#`#VRfP8P5P6P6%3C#S#;#<#U#:#>#:#6RgPTPGP7%U\#;#;#;#;#;#;#6RhP3M:?9@cD1HK8/bN#C%C5Ri1=5TRj1=6T'1'B%86146^'1'1Rk'1'1X2f'7X6=,7=X7=,7=X>e,7eXIePMPePMP5P6P6PgPTPGP7PhP3M:?9@cD%CORl/1kRk'1X2f,7fX6=,7=X7=,7=X>e%<I#6,JD=IALRIP=PMP5P6P6PgPTPGPIPhP3M:?9@cD/1kX2f,7fX6=,7=X7=PVP=PMP5PVPVPgPTPGPIPhP3M:?9@cD1=VTRk,1j,Bi%8V14V^Ri'1Rj'1,1l'1X2f,7fX6=PRPfPMPRPVPVPgPTPGPIPhP3M:?9@cD%CRRe1=RTRm/1kRn'BRo/1jRp,1lRq'1X2f%3H#<#6,JD%TLRL$07#G#G#G#G606ARHPMPRPVPVPgPTPGPIPhPHM:?9@cDPqp,1Ap,3nx0p,5LIMITp,4SINVp,4argHp,3FS0p,<SEGS_in_hullp,7HULL_okp,9argH_highp,1EPAp,1RP`Pap,2HCPbp,3HA'PDPEP5ND05PlPpP01953#21=65[Rp1=531965#2Rl[1=76\l20453P5n2001000000120000000X4=X5=RlPp^4=^5=RpP3POP:P5O3b0PoPjB03SX9%2SRS%2XRX'BP1PSPXPoP3PlPpP3PRP:P5O3b0:02enX1SP3O1ADUW3%2URU%2WRW'1P0PUPWPoP3PmPkPlPpP3PRPTP6O3b0PlPpP3PVPTP5O3b0CF:01enX@WX?UP5P3O2n2001000000121000000b1X1XP3O1n200100000021000011000b1P01K53#21465[R014531K65#2RX[1476\X1|53P5n2001000000120000000X4=X5=P0^4=^5=P3PVP^f;O3Pi1JDN=IALRL#{1HKLRL#8%6JRJ,XGRK,4LRA'11_G]14:GRN%8]14:^[RD[%8GRig00A4RVA^G]5UW3%8^\V^3i1_GJ%8J14:K[R]\NA^GJ5VVX3i%8K\V^3iP5g00ee1x:G'WPNeRNO1P]P8PNO1PDp-0RDg00fKRN#v%VNP=%t=P51s=6Cq%p=%o=RNP=1N=:R]g00hV1Z=CRCCO,YNRiPNP>P?P?P@P8En5[N%l?R8PNP=PCg01Y21N=G%R\5k=CO,YNR\P8PNPNP>P?P?PNP>P?P?PB1Z=[R[/P],LNPNP>P?P?PB1N=TR],P[,LN1PC],LNF]FjPNP>P?P?PBDiEuP8A[Ni\CMCMCM1hN@P3P61W241g36#2dAy=:5CzbDbGbHX<=X==W9%83/16145^197:197T196T'E'\#2%87147^'1[[[^<=^==^9DP3PAPRPLP;P<f?O6bCb;b:bEb:bFb;b0Pjeb8b0CFCFCFCACACACACAPdeXBPXAFP5P3O2n2001000000121000000b0X1YX0QP5P3O2n2001000000121000000b0X8_X0ZP5P3O2n2001000000121000000b0W0o"). Qed.

End Stdio.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition x_tidE (ch : acs) : expr := match kw_find (kn ch) (ELit 0) 0x63fda0 4 with Some v => v | None => ELit 0 end.
Definition hs_tid_ok (ch : acs) : bool :=
  (match kw_find (kn ch) (ELit 0) 0x63fda0 4 with Some _ => true | None => false end
   && fact_ok (kn ch) (KRange (x_tidE ch) 1 (2 ^ 31 - 1)) && seg_rw_ok asegs 0x63fda0 4)%bool.
Definition x_atexit (ch : acs) : list cell :=   (* [comment removed for export] *)
  [C1 (Z_to_bv 8 0); CB 3 (hs_blob ch 0x65fe99 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (hs_blob ch 0x65fea4 4);
   C8 (Z_to_bv 64 0x65feb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xea248); C8 (hs_word ch 0x65fec0 8)].
Definition x_libc (ch : acs) : list cell :=
  [C1 (hs_byte ch 0x6600d8); C1 (hs_byte ch 0x6600d9); C1 (hs_byte ch 0x6600da); C1 (Z_to_bv 8 0); C4 (hs_word ch 0x6600dc 4)].
Definition x_stdin (ch : acs) : list cell :=
  [CB 8 (hs_blob ch 0x102408 8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (hs_blob ch 0x102420 16); C8 (Z_to_bv 64 0);
   CB 8 (hs_blob ch 0x102438 8); C8 (Z_to_bv 64 0); CB 76 (hs_blob ch 0x102448 76); C4 (Z_to_bv 64 0xffffffff);
   CB 88 (hs_blob ch 0x102498 88)].
Fixpoint hs_gds (ch : acs) (a : Z) (gs : list gdesc) : bool :=
  match gs with
  | [] => true
  | g :: gs' => (hs_cells ch a (gd_cells g) && hs_gds ch (a + 64) gs')%bool
  end.

(* [comment removed for export] *)
Definition hs_xenv_core_ok (ch : acs) : bool :=
  (hs_tid_ok ch
   && hs_rw_cells ch 0x6600b8 [C4 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x6600d8 (x_libc ch)
   && hs_rw_cells ch 0x660540 [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x102310 [C8 (Z_to_bv 64 0x102228)]
   && hs_rw_cells ch 0x102400 [C8 (Z_to_bv 64 0x102318)]
   && hs_rw_cells ch 0x102408 (x_stdin ch) && hs_rw_cells ch 0x1024f0 [C8 (Z_to_bv 64 0x102408)]
   && hs_gds ch 0x102520 asan_gds
   && negb (Z.eqb (bv_unsigned (hs_word ch 0x1095c0 8)) 0) && hs_rw_cells ch 0x1095c0 [C8 (hs_word ch 0x1095c0 8)]
   && hs_rw_cells ch 0x109610 [C1 (Z_to_bv 8 0)]
   && hs_rw_cells ch 0x63f302 [C1 (hs_byte ch 0x63f302)] && hs_rw_cells ch 0x63f300 [C1 (hs_byte ch 0x63f300)]
   && hs_rw_cells ch 0x63f301 [C1 (hs_byte ch 0x63f301)]
   && hs_rw_cells ch 0x63f303 [C1 (hs_byte ch 0x63f303)])%bool.
Definition hs_xenv_tr_ok (ch : acs) : bool :=
  (hs_rw_cells ch TR_INCB [C1 (Z_to_bv 8 0)] && hs_rw_cells ch TR_INIT [C1 (Z_to_bv 8 0)]
   && hs_rw_cells ch 0x65fe98 (x_atexit ch)
   && hs_rw_cells ch 0x65ffb8 [C8 (Z_to_bv 64 0x8591c); C8 (hs_word ch 0x65ffc0 8)])%bool.
Definition hs_xenv_ok (ch : acs) : bool := (hs_xenv_core_ok ch && hs_xenv_tr_ok ch)%bool.

Section Xenv.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation RWC := (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').
#[local] Notation ROC := (hi_ro_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').

Lemma hi_gds : forall gs a, hs_gds ch a gs = true -> gds_at m a gs.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Xenv"] "h01Hh11ah22gsh32H1h42H2h52IHh61gp;1p;3p;2p;4p;Dp;5g000kj1BTg01YYj32Tg00LVj39Tg01ZVj36Tg002Ej1;Tg00=[j37Tg01[Pj13Tg00Fcj35Tg002ej11Tg00H]j18Tg00H@j24Tg00;>j3:Tg00;aR0j2ATg00MNj4@Tg00nIlD?Tg005Cj4<Tg00=9j5=Tg00<<j3>Tg00>;f0R1g00>[3>p=0g01\LR2#BR3P2g00dOR4p,2chR5f1R6721#0p,4FULLR7p,5modelR8p,2A'R939R:f2R;766[]1R<X23%;29251#0g00@3W0X14f3R==72;9251#0f4R>#39556R?g00@O#1#1#1#1#1#1#8R@,46=25=RA;:1%0?%0A'AP0f5R0#3955;#014;@=25>#0f6R;=72096:=P1f7R=#3955>#0140@=25=#0g00dmP:P;f9#3R0C@14;@R@f856:p,1Ap,3nx0p,5LIMITp,4SINVp,4argHp,3FS0p,<SEGS_in_hullp,7HULL_okp,9argH_highp,1EP5p,1RP7P8p,2HCP9p,3HA'P;P0P6MD?P=P@P1O2C<W4W3P6P1O2n2001000000120000000b0W0X14X5<X23X62P1D=W2o"). Qed.

Lemma clx_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Xenv"] "h01zh12Hzp;2p;1p;3p;6g00NGj2=Tg002ej10Tg00H]j12Tg00I`j23Tg00XPj2<Tg00;aj2:Tg01]Gj25Tg00<<j31Tg01]gj34Tg003Jj16Tg00R^j27Tg019nj28Tg01^Jj19Tg000Mj6;Tg00dOR0g00d1f0R1'=g00@O#0R2#2%02#0#0#0#0R2#2'3R3,<1':P0f1R4g01_Q'5R5f29101X00A4431A1054e%62R21724'8%94E;W1W0o"). Qed.

Lemma hi_tid : hs_tid_ok ch = true -> exists tid : Z, 1 <= tid < 2 ^ 31 /\ rw_cells asegs m 0x63fda0 [C4 (Z_to_bv 64 tid)].
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Xenv"] "p'0h02Hah16__sat2h21Hh32Hkh42Hfh52Hrh66__sat4h71Xh87__arithh94__ffh:6__sat1h;8__varmaph<5__with=1xi001xh>6__sat3h?4__x1h@1zhA2HshB2KrhC1bi011bhD1ei021ehE1lhF1mhG1nhH1oi031ohI3tidhJ1vi041vhK1yp&0p;1p;4p;2p;3p;6p;=p;7p;8p;Fp;<p;5p;Bg01`Pk10JTg00OCj1vTg01aPj1iTg00I;j1KTg002ej12Tg00H]j1:Tg01I;j1ETg01bPj4hTg01cPj1dTg00I`j2LTg01dMk20ITg01djj3?Tg01elj2ATg00Gbk20<Tg00j_k301Tg00;>j3XTg00;aR0j26Tg00NGR1j20Tg00XPj28Tg00LVj3uTg003Jj1HTg00R^j2BTg005^j1DTg002Ej1NTg00=[j3ITg00kaj4[Tg011cj2kTg00R<R2j1jTg00Aoj27Tg00<<j3;Tg00S`j2eTg01fjj6cTg01gmj2bTg01hnj3aTg01j0j3`Tg01jGj6_Tg01kFl=^Tg01lJk70HTg01mTk40GTg01n]j2>Tg019nj2JTg00Whj2TTg00Xlj3STg00YPk20>Tg000kj1]Tg00Z1k20;Tg00ZOk10:Tg00Zmk102Tg00[Xj2=Tg00\;k200Tg01U8j3MTg01o]j3~Tg00TBj1WTg00\^j4OTg00]mj8}Tg00^Qj2|Tg00_3j2{Tg00__j3zTg00`>j4yTg020@lFxTg021>j2tTg00VcR3j1PTg00H@R4j23Tg022Dj2FTg01H2j1sTg023Lj2rTg00BIj6QTg024Nj1wTg00lZj4qTg00Ugj1pTg00mTj4UTg001Kj1VTg00KYj1ZTg013?j1oTg005Cj4GTg003hj1YTg024oj1nTg01Foj1mTg025bj4lTg01GMm<05Tg026Ek306Tg01HPk407Tg0148k308Tg014Uk209Tg000Mj6\Tg026hj1gTg00oKk40=Tg010@j5fTg011Hk30?Tg0167k40@Tg00Bek20ATg00]Ik70BTg01U[k70CTg00b3k40DTg01IZm<0ETg027nmB0FTg00>;R5f0R6g00>[R73;p=1%26#2p=C%K6#Kp=4g00d1R8/06p=9g00dOR9f1R:g00hVP6COp=@P:g00g7R;g00gVR<P<g00h6R=P6g00i=K0Bp=<f2R>P;P<P<P=P:P6K0Cp=Rg00dmR?P>P:P6H0Dp=5g00APR@P9P9P9P3P3f5R3f4RAf3RBP>P:P6N<0Ep>03P9P9P9P9P9P9P4P6P:P>P4PBPAP3f6R4f7RCf8RDf9RENB0Fp>04p,2chRF$0J#1P2g028TRGP5%vFRH%i8RIg00@ORJ#K#2#C#4#4#4#4#2#4#2#K#2#C#C#:RKg016Q#E#E#E#ERLChRMP7g00EfRNn10110000021010200RO%dF%:JRP%2JRQ#:RR%4J#4RS#:RT'LRU00IPRV3?,AHRW+0<RX%2QRY#:RZ:01?KR[;X6%1XRX%1[R['6P0PXP[10P6R\186U'6P?p,4FULLR]p,5modelR^p,2A'R_3uR`PKg00?;Ra%2YRY#2#CRb#HRc/B6#D%NaRd3IC['6XI9Re,k9RfP6AXOW:%1ORO%1WRW'6P0POPWPfP6PM%jGR01706A;0M6RgP2PGP2PGP5P:P7PNn10110000021010200#1P2PGPGP>P6PIn10110000021010400??PV,AH#1Pf]5]4^3gP:1eG69;0MA;577A?>PV,AH#1PHPIPKPLPBP>Ecg029T1bIKRg?aLB;`HP?p,1ER2p,1ARhp,4argHRiP2PFP^P]E_RjPHA?APVRkP?Php,3nx0Rlp,5LIMITRmp,4SINVRnPip,3FS0RoP2PFp,1RRpP]P^p,2HCRqM=^P:K0HP?P2PjPkH0GP9Pe1>23,JcRe10Pe18eU'6P?P`PK1Bce#D=IadC[1TRTRe188RRk%9T188U[Rj[Rr%9RRsg00A4RtASRT:UW0RT%9U\t^0sRuP:g00ee20>8R'7PkeRvO1RwPjg00fKRx#NRy%]xRx20;9:&0:9Rz&029R{P;P<P<P=1=9PR;2009JRJ'@,<{R|1=9RR}%HS5M9RS=~9;,@J,<{5R{%W<P9PJg01Y2RJPSCO,<{9R{|G}1|{=R=P6P>17571{6>#1dAz98:CyR|b9b;b<X?9106V,6\10P:18:U'6[^?9P61>2ERE,JcPAO2b8b1b:b1P?PhPlPmPnPiPop,<SEGS_in_hullp,7HULL_okp,9argH_highP2PFPpP]P^PqP_p,3HA'PgPLP3P:MFx1t2gRg%PLR3'3%4Q#4RQ#:R_,LRRq'01>24,FL95`g[P91Bc8,Jc136K/33/0q13:K1>2DRD,FLRg55`[X@9P6P8%:bRb,TR%9b1LRbR4,88R^[R]\kASRb:VtX0s%94\t^0sPePrPTPuPwPjPAPvO1RvP]PyPx%s9R]Pz1=98RA/@A,<{P9PAPJAM9}cCO,<{5R{P=P|b9b;b<1088/6^P6b8b6b1b:b1b>b6,r8EQ138KR^/33/0q1>2C,FL95`^[P9P^1363/0q1FLE95`:[X@9P6PK%wKEQ13K3RE/0qR^A5`Kg[P?P`PK1JcD,BcRg#DR2=IadRCCqP?P`PK%pC#PCU%VC%ZC95`K%o2%Vdg00@3R2P2CG%YcRcPD%D6=Iad#Z95`KXCc%HY#YRY#]Rc%nDRdA5`K6XEcP6P^13KZR^/0qRcP9P9P1P6X=9RaP110:6#mXK9X=9PEP^PaPaPaP9P9g02:V13:6Cl,79XF9XG9PKPK179KP3PZPaPa%P6,79X=@PLPZ179ZJ03N:04PqPq179qN<051TR_%9_188q[R8\kASR_:VtX0s%9q\t^0sPePrPTPuPwPjPvP8PyPxP]Pz1=9K1=9Z6069%HQ9M9}'@,<{P=P|b9b;b<PcP6b8b6b1b:b1b>b6H07O1%NY:08Yd209YdE\Pg%gDE\CGP?P`PKPZCUP?P`PKP^H0=P?PKPZfAP`Df40?CGb7b7b7CGH0@bBb3W5W4W3XJGP6O1%WG9;0MA;5N7A?IPV,AHRH#1P5PHP5p-0P6g00FFRHPtn0110100020000XD5P2P7P6EQPH20Af6b2W5W4W3n10110300021110200P6PBP>O3b3bHX5WX4OP:P6O2n2001000000121000000b2XA[X2XP:P6O2n2001000000121000000b2W2o"). Qed.

Theorem hi_xenv : hs_xenv_ok ch = true -> XENVA m.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Xenv"] "h01Hh12HTh22j4h32a1h42j3h52o4h63tm1h73H14h82f1h92j2h:2o3h;3sech<1bh=2j1h>2o2h?2p2h@3thrhA1xhB1yhC3H10hD3H11hE3H12hF3H13hG3H15hH3H16hI3H17hJ3H18hK3H19hL3H20hM2H6hN2H7hO2H8hP2H9hQ2T1hR2T2hS2T3hT2T4hU3cdthV2j0hW2o1hX2p1hY3tidhZ1vp%0p&0p;1p;2p;3p;Dp;4p;5g02;:k10:Tg01`Pj1{Tg002ej10Tg003Jj1mTg00R^j2@Tg005^j1`Tg002Ek109Tg00i]j38Tg00Gbj27Tg02<;k100Tg00I;j12Tg004Kj1dTg02=8j1tTg01YYj3sTg01I;j1:Tg0190j3aTg019nj2qTg01;6j2lTg02>6j1kTg007Nj1=Tg02>Tj2TTg00H]j1FTg02?Rk108Tg00;>j36Tg00;aR0j21Tg00LVk307Tg02@Qk106Tg02AJk105Tg02BHk104Tg00NGk203Tg00I`k202Tg00XPk201Tg011cj24Tg003hj1pTg02CDj1~Tg01ZVj3}Tg00<<j3UTg02DBj1ZTg02D[j1zTg01EMlD9Tg000kj1yTg008Fj2JTg01DOj3RTg0167j4bTg02EXj3wTg02FUj1vTg02G6j2|Tg005Cj4QTg00kaj4STg02GWj5]Tg02HUj3jTg01Poj2oTg01Qej3uTg00=[j3VTg00>;R1f0R2g00>[3Up=3%22#0#0p=P%22#2#0#0p=^%02#0#0#0p=E%02#0#0#2p=>%02#2#2#2p=\%02#0#0#Fp=5%02#0p=n%02#0#0p=gg00?;R3f1R4;V2p=?%22#0#2#2p=X%02#0#2#2p=B%02#0#2#0p=D%22#0p=c%22#0#0#0p=A%02#0#0#0#0#0#2#0#0p=K%02#2#2#0p=e%02#2p=M%d4=V32p=H%22#0#0#2p=G%22#2#2#0p=[%02#2#0#0p=h%:2#:p=r%:2#:#:#:p=f%22#2#2#2p=Y%02#Fp=_%22#2#2#2#2#2#2#2p=Ng00dmR5f3R6f2R7AV342CSp=;P5P7P4P2CSp=CAV3429V37p=<f6R8f5S00f4R9P6P7P4P2CbCbp=L%:2#:#:#:#:#:#:#:p=I%22#2p=x1J74=V32p=ig00Ef9U12p=WP8Q00P9P6P7P4P2CQCQp=Op,2chR8$0:#3%{8R:g00@OR;#P#^#E#>#\#5R<%0;S01#nR=#g#mR>g00d1R?'@R@#`S02&093R3'?RA588RB'7RC%P;#^#E#>#X#5RD&008S03588RE'7RF%2;#B#E#D#c#A#5RG%d@R@/?3RH588RI'7RJ%K;#e#D#5RK%g;#>#>#>#M#5,@>/H3RL588RM'7RN%K;#A#E#5RO%K;#e#B#5,@>/H3RP588RQ'7RR%K;#A#>#5RS%t8S04588RT'7RU%K;#G#[#5S051@>S/H3S06588RV'7RW%g;#>#D#c#h#5RXg02ISRY5s8RZ'7R[%0;#>#D#X#A#5R\g016Q#:#rR]#:R^#fR_5a8R`,q>S07/l?S08#kRa'7Rb1H`3S09988\Rc'7Rd%0;#>#D#^#D#5S0:%m=R=/@?#=Re/?3Rf588Rg'7Rh%2;#>#Y#G#A#>#_Ri1T8iS0;#=/?3S0<588Rj'7Rk%P;#\#[#e#E#5Rl1T8lS0=#=/?3S0>588Rm'7Rn%c;#B#Y#B#E#>#FRo1T8oS0?#=/?3S0@588Rp'7Rq%c;#B#Y#B#E#B#FRr1T8rS0A#=/?3S0B588Rs'7Rtg02JOS0C=88fRug02KIS0D=88fRv'7Rw%2;#D#N#M#B#5S0E&088S0F588Rx'7Ry%P;#X#N#\#5S0G%n;#D#^#A#[#_,@>%P;#X#N#A#5=a8_S0H/H3S0I'HS0J588Rz'7R{;62%3tS0K%3{S0L'1P0Q0KQ0Lp,4FULLR{p,5modelRtp,2A'R|407R}$06R~P2Q0KQ0LA6yz2%3yS0M%3zS0N'1P0Q0MQ0NP~P2Q0MQ0NA6wx4%3wS0O%3xS0P'1P0Q0OQ0PP~P2Q0OQ0PA6uv4%3uS0Q%3vS0R'1P0Q0QQ0RP~P2Q0QQ0Rf@96qs%3qS0S%3sS0T'1P0Q0SQ0TP~P2Q0SQ0TA6np4%3nS0U%3pS0V'1P0Q0UQ0VP~P2Q0UQ0VA6km4%3kS0W%3mS0X'1P0Q0WQ0XP~P2Q0WQ0XA6hj4%3hS0Y%3jS0Z'1P0Q0YQ0ZP~P2Q0YQ0ZA6dg4%3dS0[%3gS0\'1P0Q0[Q0\P~P2Q0[Q0\A6bc4%3bS0]%3cRc'1P0Q0]PcP~P2Q0]A6[a4%3[R[%3aRa'1P0P[PaP~P2A6WZ4%3WRW%3ZRZ'1P0PWPZP~P2A6UV4%3URU%3VRV'1P0PUPVP~P2A6RT4%3RRR%3TRT'1P0PRPTP~P2A6NQ4%3NRN%3QRQ'1P0PNPQP~P2A6JM4%3JRJ%3MRM'1P0PJPMP~P2A6FI4%3FRF%3IRI'1P0PFPIP~P2A6CE4%3CRC%3ERE'1P0PCPEP~P2A6:B4%3:R:%3BRB'1P0P:PBP~P2&05}&04}g00dORb%F;Rg0032Q01#F%Y;S01#F+02-012'1P}%P;#\#Y#X#h#51@>2#`P3C;'1XYb'4AC}<ARd%p=Rj%p>RhP}PD%=6Rm%=7Rk%=4Rp%`2=<e3S0^'?S0_'?S0`C;X6h'4X;j,4jX@j,4jXUjS0a'4S0bAC}GHS0cAC}KLS0dAC}OPS0e%~}S0fQ05Q065C}S0gA}}XYS0h1q>2=Ub?#ZP}P\%d2P3C;'1XZhS0i,4hS0jQ0:=C}fS0kP}PiPmP3C;P}PlPkP3C;P}PoPpP3C;P}Pr%=2P3C;S0l'1S0m'1S0n'1X5j,4jX:j,4jX>j,4jXWjS0o,4jS0p'1S0q'1S0r'1S0s'1S0t'1S0u'1S0v'1S0w'1S0x'1Rp'1%z4PdPpp,1ARpp,3nx0Rdp,5LIMITRkp,4SINVRmp,4argHRnp,3FS0Rsp,<SEGS_in_hullRqp,7HULL_okRvp,9argH_highRup,1ERxP8p,1RRwP{Ptp,2HCRzP|p,3HA'RyP<PAP2MD9Q0bQ0xPjQ0a1T8DRAPjP}PD%=AS0aQ0`C;X6h,4hX;j,4jX@j%G;#A#E#B#M#G#F,T8RAPjP}PDQ0a%=ARAQ0_'?C;X6h,4hX;j%P;#^#E#>#X#M#_,T8R<PhP}PDQ0a%=<Q0^5<AC;X6h%2;#B#E#E#e#[#_=a8^PpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPDQ03Q00MD9FLFLQ0cQ0wPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPGPHf:MD9Q0dQ0vPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPKPLf?MD9Q0eQ0uPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPOPPfDMD9Q0fQ0t%yjRPP}PS1J_9%I_R91J_7%f9#I#I#I#I#I#I#IRO/J4Q01#2#x#N#N#N#F,@>#`%fO#IRL/J2;<3RK5<@RH5<@RG7i69<@@RDC;X2P,4PX4P,4PX9P,4PX=P,4PXVPAR8S_RAPPP}PS1J_ARAPDC;X2P,4PX4P,4PX9P,4PX=P%K;#A#h#5=R89RDPPP}PSPA1J9DRD/?G9<@@C;X2P,4PX4P,4PX9P%K;#A#\#5=R8_RGPPP}PSPA1J_GRG/?H9<D@9<@@C;X2P,4PX4P%K;#A#G#5=R8ORHPPP}PSPAAiOHK9<G@9<D@9<@@C;X2P%K;#G#B#5=R8LPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPSQ04fIMD9CbFLFLQ0feQ0gQ0sPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyQ05Q06fNMD9Q0hQ0rfS9wYXQ0jQ0qPhQ0iP`Q07=Ub?#ZR`Q099C}\P0%k2#3%W4[RY%W2%k4#3RX[%W7\X%v2P4n2001000000120000000X<1PY^<1P2Q08fYO2Q08#WP01l42#WAUb74#Z[R0AUb42#Z1l74#WR1[AUb67#Z\11|42P4n2001000000120000000XBbXAbP0^Bb^AbP2Q07P?P4O3P`P2b7b0b7b0PpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyP\Q09f]MD9CQCbQ0kQ0pPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyQ0:PffbMD9PjQ0oQ0;PjQ0<9C}iR\Q0n'1X5j,4jX:j,4jX>jQ0=PjQ0>9C}lR`Q0m'1,1\X5j,4jX:jQ0?PjQ0@9C}oR?Q0l'1,1`,1\X5jQ0AP\Q0B9C}rR\,1?Rj,1`PpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPiQ0<fgMD9P`PjPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPlQ0>flMD9P?P\PpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPoQ0@fqMD9PpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyPrQ0BfvMD9CQFOFLFLCQFOFOFOFOFOP5P}Q0CPfCSP5P}Q0DPfCSRrP}P6P7P4P2D]X3h,4hX8h,4h'1P5P}Q0D1@=g#=/?3CSR=Aj}42'1'oX?P,4PXXPR6,4PPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyQ0CPff|MD9PPP6%G;#M#Y#[#G#G#F=R8]R6PPP}P6P7P4P2D]X3h,4hX8h,4h,1rAj}62,1='oX?P%2;#D#N#M#M#D#_=R8^RPP}P6PPP4P2D]X3h,4hX8hR7,4hRo,1rAj}6P,1=PrPoPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyQ0DPff{MD9PhP7%2;#D#N#M#A#5=a8_R_PhP}P6PPP_P2D]X3hQ0HP5P}g02LC1J]6Q021@>g#`g02M<,@>g02N;,@>#d1H_35<@'H9i^P3<5<eCSP5P}g02O7g02P1,@>Q0I'HCSPpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyQ0EQ0Fp+01AMD9PpPdPkPmPnPsPqPvPuPxP8PwP{PtPzP|PyQ0GQ0Jp+01FMD9CQP}P6PPP_Q0HD]eFLCQ3uFLFOP~eXMBX0:P4P2O2n2001000000121000000b0XNEX0CP4P2O2n2001000000121000000b0XOIX0FP4P2O2n2001000000121000000b0XPMX0JP4P2O2n2001000000121000000b0XCQX0NP4P2O2n2101000000121000000b0XDTX0RP4P2O2n2101000000121000000b0XEVX0UP4P2O2n2101000000121000000b0XFZX0WP4P2O2n2101000000121000000b0X7aX0[P4P2O2n2101000000121000000b0XGcW0P4P2O2n2101000000121000000b0WHW0P4P2O2n2101000000121000000b0WIW0P4P2O2n2101000000121000000b0WJW0P4P2O2n2101000000121000000b0WKW0P4P2O2n2101000000121000000b0WLW0P4P2O2n2101000000121000000b0WRWQP4P2O2n2001000000121000000b1WSW1P4P2O2n2001000000121000000b1WTW1P4P2O2n2001000000121000000b1W1W0P4P2O2n2101000000121000000b0W0o"). Qed.

End Xenv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hs_clx_ok (ch : acs) : bool := (hs_out_ok ch && hs_err_ok ch && hs_xenv_ok ch)%bool.

Section Clx.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

(* [comment removed for export] *)
Theorem hi_clx : forall LIB : mem -> Prop, LIB m -> hs_clx_ok ch = true ->
  CLX OUT_repA ERR_repA XENVA LIB stdout_init m.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffCLX ()) ["Clx"] "h01Hh11vh22Erh31Gh42H1h52H2h62H3h72HLh83LIBh92Ssh:2Trh;1ah<1gp;1p;3p;2p;4p;Bp;6g002ej15Tg003Jj1:Tg003hj1;Tg00R<j1STg00LVj3QTg02Pmj1ETg0170j1@Tg01K=j1?Tg00Gbj2>Tg02;:j1<Tg00;>j38Tg00;aR0j20Tg02Qmj1RTg004Kj1PTg002Ej1MTg00=[j37Tg00MNj4DTg011cj26Tg005^j1CTg00kaj49Tg00H]j1BTg00H@j2ATg00oKj4FTg007Nj1GTg01;SR1j2HTg01P2R2j1ITg02@QR3j1JTg02S4lBKTg02T1lB=Tg02TnlBLTg005Cj42Tg00<<j3NTg02Ulj6OTf0R4#5#5p=1g00>;g00>[7N4p=4P1P2P3f1R3g01J?R2P4EOp=3g00@O#5#1R1#5#1R5#:#;R6%:1#;R1#S[p-0[P4p,4FULLR7p,5modelR8p,2A'R93QR:O1p,2chR;#E#4%@;R<%?;R='>R>%<;R?;84%4>R>%4?R?'0P0P>P?f4/3:P4A8<=3%4<R<%4=R='0P0P<P=f9R@/3:P4%R:g00dmRAP:g02Vbg00?;RB%P4%MBRC37CDX<6,66RDPAP:g02W_%C4=7BCC9X16,66R6PAP:g02XYRE%15#1#1#1#1#B,AECFREPAP:g02KI%G4=7BCC9X11,61R1'0RC'0RB'0P0PDPBf>RA/3:P4P0P6PCfBR5/3:P4P0PEP1fF/3:P41H2:%I:R2%J:R0fIRFP:O1RG106ERH,0DRI'0RJ'0RK'0p,1ARLp,3nx0RMp,5LIMITRNp,4SINVROp,4argHRPp,3FS0RQp,<SEGS_in_hullRRp,7HULL_okRSp,9argH_highRTp,1ERUP;p,1RRVP7P8p,2HCRWP9p,3HA'RXPAMBKP2PKPLPMPNPOPPPQPRPSPTPUP;PVP7P8PWP9PXf=MB=P0PJPLPMPNPOPPPQPRPSPTPUP;PVP7P8PWP9PXP5MBLPGPIfHPDPHP@P6PEf5P3C2C2C2C2C2C213F:eX:1X9EP3P4O2n2001000000121000000X0CX26P3P4O2n2001000000121000000X0BX3DP3P4O2n2001000000121000000b;X5=X4<P3P4O2n2001000000121000000b0X6?X0>P3P4O2n2001000000121000000b0W0W7W8o"). Qed.

End Clx.

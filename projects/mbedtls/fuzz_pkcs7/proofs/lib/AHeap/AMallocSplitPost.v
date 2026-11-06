(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow ARt AUnw.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AModelX AVmLib AVm AVst AW_DepotB AW_DepotTop AW_MallocB HMLib HM HMFrame AHeapR AMallocPost AJ.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AMallocSplitPost () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.AHeap.AModel.ahst"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.AHeap.AModel.A_TP"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.AHeap.AVst.HK"; "OSSVerify.KrLib.AHeap.AHeapR.AL0"; "OSSVerify.KrLib.AHeap.AJ.J"; "OSSVerify.KrLib.AHeap.AModel.alayout"; "OSSVerify.KrLib.AHeap.AModel.h_L"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.AHeap.AModel.a_sech"; "OSSVerify.KrLib.AHeap.AModel.h_acct"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.AHeap.AModel.h_havol"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.AHeap.AModelX.hfr"; "OSSVerify.KrLib.AHeap.AVm.vcs"; "OSSVerify.KrLib.AHeap.AVst.vst_of"; "OSSVerify.KrLib.LibA.ARt.presA"; "OSSVerify.KrLib.AHeap.AModel.l_stk_hi"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.AHeap.AMallocPost.img_keep"; "ARUN_1.Post.regs_kept"; "OSSVerify.KrLib.AHeap.HM.HMc"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"].

Section ARUN_1. Context {hAR : arun}.

Section Post.
  Variable STKLO : Z.
  Let R := R0 STKLO.

  (* [comment removed for export] *)
  Definition regs_kept (n : Z) (h h' : ahst) : Prop :=
    forall j, (from_primary n = false \/ j <> pclass n) -> h_reg h' j = h_reg h j.

  Definition mallocH_postN (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (LB LF : list (Z * Z)) (n lo d SP : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AMallocSplitPost ()) "Lcf,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.$5.Lh',$5.(6.(7.$0.R12.(8.(9.(:.O19.(;.&40.O3.)O18.(;.&40.$<.)R11.R10.R?.O17.O16.(;.&40.=)R>.R=.R<.R;.R:.R9.R8.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R7.R6.R5.R4.)O;.(=.O19.)O:.(>.(2.&40.))R3.(?.$10.))R2.))(6.(11.$10.R3.)(6.(12.$10.R3.O5.O3.)(6.(13.O1.R2.)(6.(14.$10.O2.R3.)(6.(15.VhAR,$16.R1.R2.)(6.(17.R3.R2.)(6.(7.$18.(19.R1.)(19.O9.))(6.(7.(1:.(1;.$1<.$1<.))(1=.(1>.R1.))(1=.(1>.O9.)))(6.(1?.(20.R1.)(21.(20.O9.)(22.+2.O6.)))(6.(1?.(23.R1.)(21.(23.O9.)(21.O4.+3.)))(6.Px,$1<.P,(24.$16.(25.O9.)R1.)(24.$16.(25.R3.)R2.)(6.(26.$10.VR,O8.O7.O3.VSTKLO,(27.(19.O9.))(28.$29.)O2.R3.)(6.(2:.O2.R3.)(6.(2;.O6.O9.R1.)(2<.VhAR,R1.O8.O7.R3.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition mallocH_postC (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (LB LF : list (Z * Z)) (n lo d SP : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AMallocSplitPost ()) "Lcf,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.$5.Lh',$5.(1.$1<.Lres,$1<.(6.(7.$0.R13.(8.(9.(:.O19.(;.&40.O3.)O18.(;.&40.$<.)R12.R11.R10.O17.O16.(;.&40.R1.)R?.R>.R=.R<.R;.R:.R9.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R8.R7.R6.R5.)O;.(=.O19.)O:.(>.(2.&40.))R4.(?.$10.))R3.))(6.(11.$10.R4.)(6.(12.$10.R4.O5.O3.)(6.(13.O1.R3.)(6.(14.$10.O2.R4.)(6.(15.VhAR,$16.R2.R3.)(6.(17.R4.R3.)(6.(7.$18.(19.R2.)(19.O9.))(6.(7.(1:.(1;.$1<.$1<.))(1=.(1>.R2.))(1=.(1>.O9.)))(6.(1?.(20.R2.)(21.(20.O9.)(22.+2.O6.)))(6.(1?.(23.R2.)(21.(23.O9.)(21.O4.+3.)))(6.Px,$1<.P,(24.$16.(25.O9.)R1.)(24.$16.(25.R4.)R2.)(6.(26.$10.VR,O8.O7.O3.VSTKLO,(27.(19.O9.))(28.$29.)O2.R4.)(6.(2:.O2.R4.)(6.(2;.O6.O9.R2.)(6.(7.$1<.(2=.R1.+10.)=)(6.(2>.VR,O8.O7.R1.O6.)(6.(2?.(1?.(21.R1.O6.)VSTKLO,)(1?.(27.(19.O9.))R1.))(6.(2<.VhAR,R2.(30.(1;.$1<.$1<.)(31.$1<.$1<.R1.O6.)O8.)O7.R4.)(1.(1:.(2.&8.))Ljunk,(1:.(2.&8.))(32.$10.R5.R2.(30.$33.(34.(35.O6.)R1.)(28.$33.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
End Post.

End ARUN_1.

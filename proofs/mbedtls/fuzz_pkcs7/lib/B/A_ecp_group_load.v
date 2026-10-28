(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA
     A_mpi_copy A_mpi_bitlen A_ecp_defs A_ecp_statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_group_load () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "gl_sw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"].


(* [comment removed for export] *)
Definition gl_init_cells (m : mem) (A id : Z) (idpad pP pA pB pX pY pZ pN hpad : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load ()) "(0.(1.$2.O<.O;.(3.$4.(5.(6.&40.O:.))(3.$4.(5.O9.)(7.$4.))))(0.(1.$2.O<.(8.O;.+8.)(9.=(6.&40.+1.)=O8.))(0.(1.$2.O<.(8.O;.+18.)(9.=(6.&40.+1.)=O7.))(0.(1.$2.O<.(8.O;.+28.)(9.=(6.&40.+1.)=O6.))(0.(1.$2.O<.(8.O;.+38.)(9.=(6.&40.+1.)=O5.))(0.(1.$2.O<.(8.O;.+48.)(9.=(6.&40.+1.)=O4.))(0.(1.$2.O<.(8.O;.+58.)(9.=(6.&40.+1.)=O3.))(0.(1.$2.O<.(8.O;.+68.)(9.=(6.&40.+1.)=O2.))(1.$2.O<.(8.O;.+78.)(3.$4.(:.(6.&40.=))(3.$4.(:.(6.&40.=))(3.$4.(5.(6.&40.=))(3.$4.(5.O1.)(3.$4.(:.(6.&40.=))(3.$4.(:.(6.&40.=))(3.$4.(:.(6.&40.=))(3.$4.(:.(6.&40.=))(3.$4.(:.(6.&40.=))(3.$4.(:.(6.&40.=))(7.$4.))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition gl_sw_cells (m : mem) (A id : Z) (idpad pP pA pB pX pY pZ pN hpad : word) : Prop :=
  let ca := A_CA id in
  rw_cells asegs m A [C4 (Z_to_bv 64 id); C4 idpad]
  /\ rw_cells asegs m (A + 8) (mpi_cells (ca_P ca) (Z_to_bv 64 1) (Z.of_nat (length (cP id))) pP)
  /\ rw_cells asegs m (A + 24) (mpi_cells (if has_A id then ca_A ca else 0) (Z_to_bv 64 1) (if has_A id then Z.of_nat (length (cA id)) else 0) pA)
  /\ rw_cells asegs m (A + 40) (mpi_cells (ca_B ca) (Z_to_bv 64 1) (Z.of_nat (length (cB id))) pB)
  /\ rw_cells asegs m (A + 56) (mpi_cells (ca_GX ca) (Z_to_bv 64 1) (Z.of_nat (length (cGX id))) pX)
  /\ rw_cells asegs m (A + 72) (mpi_cells (ca_GY ca) (Z_to_bv 64 1) (Z.of_nat (length (cGY id))) pY)
  /\ rw_cells asegs m (A + 88) (mpi_cells A_ONE (Z_to_bv 64 1) 1 pZ)
  /\ rw_cells asegs m (A + 104) (mpi_cells (ca_N ca) (Z_to_bv 64 1) (Z.of_nat (length (cN id))) pN)
  /\ rw_cells asegs m (A + 120) [C8 (Z_to_bv 64 (core_bitlen (cP id) (Z.of_nat (length (cP id))))); C8 (Z_to_bv 64 (core_bitlen (cN id) (Z.of_nat (length (cN id)))));
                                C4 (Z_to_bv 64 1); C4 hpad; C8 (Z_to_bv 64 (ca_modp ca)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                C8 (Z_to_bv 64 (ca_T ca)); C8 (Z_to_bv 64 0)].

Definition gl_sw_post (R : art_layout) (HIA : artA asegs R) (h : HST asegs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A id : Z) (idpad pP pA pB pX pY pZ pN hpad : word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load ()) "Lms',$;.(<.(=.&40.)Lt0,(=.&40.)(<.(=.&40.)Lt1,(=.&40.)(<.(=.&40.)Lt2,(=.&40.)(<.(=.&40.)La1,(=.&40.)(<.(=.&40.)La2,(=.&40.)(<.(=.&40.)La3,(=.&40.)(<.(=.&40.)La4,(=.&40.)(<.(=.&40.)La5,(=.&40.)(<.(=.&40.)La6,(=.&40.)(<.(=.&40.)La7,(=.&40.)(<.(=.&40.)Lt3,(=.&40.)(<.(=.&40.)Lt4,(=.&40.)(<.(=.&40.)Lt5,(=.&40.)(<.(=.&40.)Lt6,(=.&40.)(<.P,(=.&40.)(>.(=.&8.))Lm',P,(=.&40.)(>.(=.&8.))(0.(?.$;.R10.(10.(11.O1?.O1>.O1=.O1<.R?.R>.R=.O1;.O1:.(6.&40.=)R<.R;.R:.R9.R8.R7.R6.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.R5.R4.R3.R2.)O?.(12.O1?.)O>.(13.(=.&40.))R1.(14.$2.)))(0.(15.(3.(16.$17.$17.)(18.$17.$17.O=.(8.O=.+<0.))(3.(16.$17.$17.)(18.$17.$17.O2.(19.&40.O1>.))(7.(16.$17.$17.))))O1.R1.)(0.(1:.$2.O1.R1.)(0.(1;.$2.R1.)(0.(1<.R1.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.)(0.(1=.$2.R1.O2.(19.&40.O1>.))(1>.$2.O24.O23.O22.O21.O20.R1.))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Ltac solve_load_shadow0_g :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 ?E) 1%nat] =>
      let c := shadow_client_of E in
      match goal with
      | H : aobj segs ?L ?CS m ?A ?k |- _ =>
          first [ rewrite (aobj_shadow0_at segs L CS m A k c (c - 2) E H ltac:(qlia) ltac:(clear; lia) ltac:(qlia) ltac:(qlia) ltac:(shadow_addr_eq))
                | rewrite (aobj_shadow0_at segs L CS m A k c (c - 4) E H ltac:(qlia) ltac:(clear; lia) ltac:(qlia) ltac:(qlia) ltac:(shadow_addr_eq))
                | rewrite (aobj_shadow0_at segs L CS m A k c (c - 6) E H ltac:(qlia) ltac:(clear; lia) ltac:(qlia) ltac:(qlia) ltac:(shadow_addr_eq)) ];
          load_post
      end
  end.
Ltac solve_load ::= first [ solve_load_base | solve_load_shadow0 | solve_load_shadow0_g | solve_load_image ].

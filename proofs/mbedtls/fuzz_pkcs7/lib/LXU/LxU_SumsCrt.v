(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA AEvt HeapIface PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtStmts CrtFacts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxRun LxDenot LxSoundRun LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsHeapO.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_LxP_SumsCrt () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XB"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.X509_GET_DATES_STACK"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "havoc11"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.X509_GET_UID_STACK"; "havoc12"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.x509_get_dates_stmt"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_validG"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "SUM_getdatesP"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.x509_get_uid_stmt"; "SUM_getuidP"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_hress"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okMR"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.SInvFacts.fp_avoids"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_P"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_opq"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_no_layout"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_fprop"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.objP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeapO.cwoP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeapO.croP"; "PkParse.blkP"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.eq"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.pk_rep"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMXH"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.PK_PARSE_STACK"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FProp"; "havoc16'"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.heapcall"; "HC_pkparseP"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.hres"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.pk_parse_subpubkey_stmt"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_validHR"; "blkP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.hpP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.cwP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeap.lawP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeapO.lawPX"; "lawPXS"; "RpkP"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundRun.tgt_aevtM"; "SUM_pkparseP"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.summary"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeapO.RnameP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_heapkit"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_own"; "Stdlib.Sorting.Permutation.Permutation"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_ok"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.eo_san_next"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.eo_akid_next"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.eo_pol_next"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.eo_eku_next"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.SEQ_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.X509_GET_CRT_EXT_STACK"; "havoc17"; "HC_crtextP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsHeapO.wchunks"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ej0"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ej1"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ej2"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ej3"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ej4"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_junk"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_cells"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.x509_get_crt_ext_stmt"; "RextP"; "SUM_crtextP"].


Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Notation "a .- b" := (EAdd a (EMulC (-1) b)) (at level 50, left associativity).
(* [comment removed for export] *)
Definition havoc10 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(0.(1.$2.$3.)(4.$2.$3.+:.^:.)(0.(1.$2.$3.)(4.$2.$3.+5.^;.)(0.(1.$2.$3.)(4.$2.$3.+6.^<.)(0.(1.$2.$3.)(4.$2.$3.+7.^=.)(0.(1.$2.$3.)(4.$2.$3.+;.^>.)(0.(1.$2.$3.)(4.$2.$3.+<.^?.)(0.(1.$2.$3.)(4.$2.$3.+=.^10.)(0.(1.$2.$3.)(4.$2.$3.+>.^11.)(0.(1.$2.$3.)(4.$2.$3.+?.^12.)(0.(1.$2.$3.)(4.$2.$3.+10.^13.)(0.(1.$2.$3.)(4.$2.$3.+11.^14.)(0.(1.$2.$3.)(4.$2.$3.+1<.^15.)(0.(1.$2.$3.)(4.$2.$3.+1=.^16.)(0.(1.$2.$3.)(4.$2.$3.+1>.^17.)(0.(1.$2.$3.)(4.$2.$3.+1?.^18.)(5.(1.$2.$3.)))))))))))))))))")
(* [comment removed for export] *).
Definition havoc12 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(0.(1.$2.$3.)(4.$2.$3.+:.^<.)(0.(1.$2.$3.)(4.$2.$3.+5.^=.)(0.(1.$2.$3.)(4.$2.$3.+6.^>.)(0.(1.$2.$3.)(4.$2.$3.+7.^?.)(0.(1.$2.$3.)(4.$2.$3.+;.^10.)(0.(1.$2.$3.)(4.$2.$3.+<.^11.)(0.(1.$2.$3.)(4.$2.$3.+=.^12.)(0.(1.$2.$3.)(4.$2.$3.+>.^13.)(0.(1.$2.$3.)(4.$2.$3.+?.^14.)(0.(1.$2.$3.)(4.$2.$3.+10.^15.)(0.(1.$2.$3.)(4.$2.$3.+11.^16.)(0.(1.$2.$3.)(4.$2.$3.+1<.^17.)(0.(1.$2.$3.)(4.$2.$3.+1=.^18.)(0.(1.$2.$3.)(4.$2.$3.+1>.^19.)(0.(1.$2.$3.)(4.$2.$3.+1?.^1:.)(5.(1.$2.$3.)))))))))))))))))")
(* [comment removed for export] *).
Definition havoc11 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(0.(1.$2.$3.)(4.$2.$3.+:.^;.)(0.(1.$2.$3.)(4.$2.$3.+5.^<.)(0.(1.$2.$3.)(4.$2.$3.+6.^=.)(0.(1.$2.$3.)(4.$2.$3.+7.^>.)(0.(1.$2.$3.)(4.$2.$3.+;.^?.)(0.(1.$2.$3.)(4.$2.$3.+<.^10.)(0.(1.$2.$3.)(4.$2.$3.+=.^11.)(0.(1.$2.$3.)(4.$2.$3.+>.^12.)(0.(1.$2.$3.)(4.$2.$3.+?.^13.)(0.(1.$2.$3.)(4.$2.$3.+10.^14.)(0.(1.$2.$3.)(4.$2.$3.+11.^15.)(0.(1.$2.$3.)(4.$2.$3.+1<.^16.)(0.(1.$2.$3.)(4.$2.$3.+1=.^17.)(0.(1.$2.$3.)(4.$2.$3.+1>.^18.)(0.(1.$2.$3.)(4.$2.$3.+1?.^19.)(5.(1.$2.$3.)))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SUM_getdatesP (pc : Z) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(6.O1.$7.#:.#16.#2.(0.(1.$2.$3.)(4.$2.$3.+:.^1.)(0.(1.$2.$3.)(4.$2.$3.+;.^2.)(0.(1.$2.$3.)(4.$2.$3.+<.^3.)(0.(1.$2.$3.)(4.$2.$3.+=.^4.)(0.(1.$2.$3.)(4.$2.$3.+2.^5.)(5.(1.$2.$3.)))))))(0.(1.$3.$8.)(4.$3.$8.^:.#2.)(5.(1.$3.$8.)))(9.$3.)(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^6.))(5.$=.)))(0.$:.(;.(<.^3.)(0.$=.(?.&30.^2.)(5.$=.)))(5.$:.)))(10.(1.$3.$3.)(4.$3.$3.^7.^5.))(0.(1.(1.$3.$3.)$3.)(4.(1.$3.$3.)$3.(4.$3.$3.^8.^9.)^1.)(5.(1.(1.$3.$3.)$3.)))(5.$:.)(0.$11.(12.(<.^4.)(13.(<.^3.)(14.+18.)))(0.$11.(15.(<.^8.)(<.^6.))(0.$11.(15.(<.^6.)(<.^2.))(0.$11.(15.(<.^2.)(13.(<.^8.)(<.^9.)))(0.$11.(16.(13.(<.^8.)(<.^9.))(14.(17.+2.+3?.)))(0.$11.(18.(<.^1.)(14.+8.)(<.^3.)(14.+30.))(0.$11.(18.(<.^1.)(14.+8.)(<.^8.)(<.^9.))(0.$11.(18.(<.^3.)(14.+30.)(<.^8.)(<.^9.))(0.$11.(19.(1:.^1.)&3.)(0.$11.(19.(1:.^3.)&3.)(0.$11.(16.(14.=)(<.^1.))(0.$11.(16.(14.=)(<.^3.))(0.$11.(16.(14.=)(<.^8.))(0.$11.(15.(<.^7.)(13.(<.^5.)(1;.-1.(14.$1<.))))(0.$11.(15.(<.^:.)(<.^7.))(0.$11.(19.(1:.^5.)&4.)(0.$11.(16.(<.^5.)(14.(17.+2.+40.)))(0.$11.(1=.(13.(<.^1.)(14.+8.))(<.^7.)(<.^5.)(<.^1.))(0.$11.(1=.(13.(<.^3.)(14.+30.))(<.^7.)(<.^5.)(<.^3.))(0.$11.(1=.(13.(<.^8.)(<.^9.))(<.^7.)(<.^5.)(<.^8.))(5.$11.)))))))))))))))))))))(0.(1.$1>.$1>.)(4.$1>.$1>.(<.^1.)(13.(<.^1.)(14.+8.)))(0.(1.$1>.$1>.)(4.$1>.$1>.(<.^3.)(13.(<.^3.)(14.+30.)))(0.(1.$1>.$1>.)(4.$1>.$1>.(13.(<.^5.)(1;.-1.(14.$1<.)))(<.^5.))(5.(1.$1>.$1>.)))))$1?.(0.$:.(20.(<.^7.)(<.^5.))(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^1:.))(5.$=.)))(0.$:.(;.(<.^3.)(0.$=.(>.&8.(<.^1;.))(0.$=.(>.&8.(<.^1<.))(0.$=.(>.&8.(<.^1=.))(0.$=.(>.&8.(<.^1>.))(0.$=.(>.&8.(<.^1?.))(0.$=.(>.&8.(<.^20.))(5.$=.))))))))(5.$:.))))(0.$11.(16.(14.-3000.)(<.^;.))(0.$11.(15.(<.^;.)(14.=))(0.$11.(15.(<.^6.)(<.^1:.))(0.$11.(15.(<.^1:.)(<.^2.))(5.$11.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SUM_getuidP (pc : Z) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(6.O1.$7.#;.#13.#4.(0.(1.$2.$3.)(4.$2.$3.+:.^1.)(0.(1.$2.$3.)(4.$2.$3.+;.^2.)(0.(1.$2.$3.)(4.$2.$3.+<.^3.)(0.(1.$2.$3.)(4.$2.$3.+=.^4.)(0.(1.$2.$3.)(4.$2.$3.+2.^5.)(5.(1.$2.$3.)))))))(0.(1.$3.$8.)(4.$3.$8.^;.#2.)(5.(1.$3.$8.)))(9.$3.)(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^6.))(5.$=.)))(0.$:.(;.(<.^3.)(0.$=.(?.&4.^2.)(0.$=.(>.&4.(<.^:.))(0.$=.(?.&8.^3.)(0.$=.(?.&8.^4.)(5.$=.))))))(5.$:.)))(10.(1.$3.$3.)(4.$3.$3.^7.^5.))(0.(1.(1.$3.$3.)$3.)(4.(1.$3.$3.)$3.(4.$3.$3.^8.^9.)^1.)(5.(1.(1.$3.$3.)$3.)))(5.$:.)(0.$11.(15.(<.^8.)(<.^6.))(0.$11.(15.(<.^6.)(<.^2.))(0.$11.(15.(<.^2.)(13.(<.^8.)(<.^9.)))(0.$11.(16.(13.(<.^8.)(<.^9.))(14.(17.+2.+3?.)))(0.$11.(18.(<.^1.)(14.+8.)(<.^3.)(14.+18.))(0.$11.(18.(<.^1.)(14.+8.)(<.^8.)(<.^9.))(0.$11.(18.(<.^3.)(14.+18.)(<.^8.)(<.^9.))(0.$11.(19.(1:.^1.)&3.)(0.$11.(19.(1:.^3.)&3.)(0.$11.(16.(14.=)(<.^1.))(0.$11.(16.(14.=)(<.^3.))(0.$11.(16.(14.=)(<.^8.))(0.$11.(15.(14.=)(<.^4.))(0.$11.(16.(<.^4.)(14.+10.))(0.$11.(15.(<.^7.)(13.(<.^5.)(1;.-1.(14.$21.))))(0.$11.(15.(<.^;.)(<.^7.))(0.$11.(19.(1:.^5.)&4.)(0.$11.(16.(<.^5.)(14.(17.+2.+40.)))(0.$11.(1=.(13.(<.^1.)(14.+8.))(<.^7.)(<.^5.)(<.^1.))(0.$11.(1=.(13.(<.^3.)(14.+18.))(<.^7.)(<.^5.)(<.^3.))(0.$11.(1=.(13.(<.^8.)(<.^9.))(<.^7.)(<.^5.)(<.^8.))(5.$11.))))))))))))))))))))))(0.(1.$1>.$1>.)(4.$1>.$1>.(<.^1.)(13.(<.^1.)(14.+8.)))(0.(1.$1>.$1>.)(4.$1>.$1>.(<.^3.)(13.(<.^3.)(14.+18.)))(0.(1.$1>.$1>.)(4.$1>.$1>.(13.(<.^5.)(1;.-1.(14.$21.)))(<.^5.))(5.(1.$1>.$1>.)))))$22.(0.$:.(20.(<.^7.)(<.^5.))(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^1;.))(5.$=.)))(0.$:.(;.(<.^3.)(0.$=.(>.&4.(<.^1<.))(0.$=.(>.&4.(<.^:.))(0.$=.(>.&8.(<.^1=.))(0.$=.(>.&8.(<.^1>.))(5.$=.))))))(5.$:.))))(0.$11.(16.(14.-3000.)(<.^<.))(0.$11.(15.(<.^<.)(14.=))(0.$11.(15.(<.^6.)(<.^1;.))(0.$11.(15.(<.^1;.)(<.^2.))(5.$11.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Section Valid.
  Variable L : heap_layout.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L1667477918.500000;S2bs2Hl1B1H". (* [comment removed for export] *)
  Lemma le4_of_bytes : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
  Proof.
    intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
    pose proof (PropExec.bytes_le_to_Z_bound bs) as B. rewrite Hl in B. pose proof (PropExec.bytes_le_to_Z_nonneg bs).
    rewrite Z.mod_small by (cbn in B; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blob48_words : forall m A (tb : list byte), rw_cells usegs m A [CB 48 tb] -> rw_cells usegs m A (wchunks 6 tb).
  Proof.
    intros m A tb H. pose proof H as H0. destruct H as [[WF _] _]. cbn in WF. destruct WF as [L48 _].
    eapply rw_cells_reshape; [exact H0| apply wchunks_wf|]. rewrite (wchunks_bytes 6 tb) by (rewrite L48; reflexivity). cbn. rewrite app_nil_r. reflexivity.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L20630336644.105L21493275511.80 L22371959134.105L23760894054.79 L23969904845.80 L25638568605.80 L30041743229.79 L30469644891.105L58972692712.80 L61490178525.105L68314649325.80 00000V01M02302e04H05?05\06:06k07I08>S2PP3END2TM2SP1P2bs3AL13AL23SPA2p'3Hp'S2PP2TM2SP3BUF4BLEN2bs3HBL2D12D22D33AL13AL23NZ13NZ23SPAS2PP3END2TM2SP1P2bs3AL13AL23SPA2p'3Hp'S1L2PP2TM2SP2LO2bs3AL13AL23NZ13NZ23SLO3ACL3SPA3ACPS1L2PP3END2TM2SP1P2LO3BUF4BLEN2bs3HBL2B12B22B32D12D22D33AL13AL23NZ13NZ23NZ33ACL3SPA3DS13DS23DS33ACPS2PP2TM2SP3BUF4BLEN2bs3HBL2D12D22D33AL13AL23NZ13NZ23SPAS2PP2TM2SP2bs3AL13AL23SPA3SPBS2PP2TM2SP2bs3AL13AL23SPA1r2HrS2PP2TM2SP3BUF4BLEN2bs3HBL2B43AL13AL23NZ13NZ23SPAS2PP2TM2SP2bs3AL13AL23SPA1r2HrS2PP3END2TM2SP3BUF4BLEN2bs3HBL2B33AL13AL23NZ13NZ23SPA". (* [comment removed for export] *)
  Lemma sum_getdatesP_valid : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PAL,$23.Pg0,$2.Pg1,$2.PGSX,(24.$2.)P,(25.$26.VL,R5.)(27.$26.R5.(0.$2.R4.(0.$2.R3.(0.$2.(28.VL,)R2.)))(29.R6.))")
(* [comment removed for export] *).
  Proof.
    intros pc AL g0 g1 GSX DATES. unfold SUM_getdatesP, havoc11, q. lx_sum_unfold.
    intros PP END TM TM24 SP P LO BUF BLEN ACE bs tb CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros ALLCS _ MI GA R10 R11 R12 R13 R2 ST HPP HTM [HBUF HBL] E24 B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 SLO ACL SPA SPB DS1 DS2 DS3.
    apply (evt_evtA_all usegs AL CS _ _ ALLCS). subst x10 x11 x12 x13 x2. rewrite E24. subst ACE.
    pose proof (@alloc_ceiling_pos L) as ACP.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64, X509_GET_DATES_STACK in *; lia).
    unfold x509_get_dates_stmt in DATES.
    eapply evt_cut.
    { eapply (DATES x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 _ _ _ _ x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP TM P END BUF LO bs tb);
        rewrite ?HSP, <- ?HBL; first [eassumption | reflexivity | lia]. }
    clear DATES. intros ms' POST. unfold x509_get_dates_post in POST. rewrite ?HSP in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & tb' & -> & MU & WM & MI' & -> & Hr & HPP' & HTM' & ST' & Hp').
    apply blob48_words in HTM'. cbn [wchunks] in HTM'.
    apply evt_done.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L20630336644.115L22371959134.115L23760894054.83 L23969905140.88 L25638568868.88 L30041743229.83 L30469644891.115L37784292690.88 L58972692945.88 L61490178525.115L61950379822.88 L68314649556.88 00000j01d02X04O05Z06906k07a08f09X0:c0;lS2PP3END4UIDA2SP1P2bs2b22b32b43AL13AL23SPA2L22L32L42p'3Hp'S2PP3END4UIDA2SP1P2bs2b22b32b43AL13AL23SPA2L22L32L42p'3Hp'S1L2PP4UIDA2SP2LO2bs3AL13AL23NZ13NZ23SLO3ACL3SPA3ACPS1L2PP3END4UIDA2SP1P2LO3BUF4BLEN2bs2b22b32b43HBL2B12B22B32D12D22D33AL13AL23NZ13NZ23NZ33ACL3SPA3DS13DS23DS33ACP2L22L32L4S2PP4UIDA2SP3BUF4BLEN2bs2b22b32b43HBL2D12D22D33AL13AL23NZ13NZ23SPA2L22L32L4S2PP4UIDA2SP2bs3AL13AL23SPA3SPBS2PP4UIDA2SP2bs2b22b32b43AL13AL23SPA2L22L32L41r2HrS2PP4UIDA1N2SP2bs2b22b32b43AL13AL22N03N163SPA2L22L32L4S2PP4UIDA2SP3BUF4BLEN2bs2b22b32b43HBL2B43AL13AL23NZ13NZ23SPA2L22L32L4S2PP4UIDA2SP2bs2b22b32b43AL13AL23SPA2L22L32L41r2HrS2PP4UIDA2SP3BUF4BLEN2bs2b22b32b43HBL2D12D22D33AL13AL23NZ13NZ23SPA2L22L32L4S2PP3END4UIDA2SP3BUF4BLEN2bs2b22b32b43HBL2B33AL13AL23NZ13NZ23SPA2L22L32L4". (* [comment removed for export] *)
  Lemma sum_getuidP_valid : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PAL,$23.Pg0,$2.Pg1,$2.PGSX,(24.$2.)P,(2:.$26.VL,R5.)(27.$26.R5.(0.$2.R4.(0.$2.R3.(0.$2.(28.VL,)R2.)))(2;.R6.))")
(* [comment removed for export] *).
  Proof.
    intros pc AL g0 g1 GSX UID. unfold SUM_getuidP, havoc12, q. lx_sum_unfold.
    intros PP END UIDA N SP P LO BUF BLEN PAD ACE bs b2 b3 b4 CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros ALLCS _ MI GA R10 R11 R12 R13 R2 ST HPP HU [HBUF HBL] B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 N0 N16 SLO ACL SPA SPB DS1 DS2 DS3.
    apply (evt_evtA_all usegs AL CS _ _ ALLCS). subst x10 x11 x12 x13 x2. subst ACE.
    pose proof (@alloc_ceiling_pos L) as ACP.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64, X509_GET_UID_STACK in *; lia).
    (* [comment removed for export] *)
    assert (L2 : length b2 = 4%nat /\ length b3 = 8%nat /\ length b4 = 8%nat) by (destruct HU as [[WF _] _]; cbn in WF; tauto).
    destruct L2 as (L2 & L3 & L4).
    assert (HU' : rw_cells usegs m UIDA [C4 (le_bytes_to_word b2); C4 (Z_to_bv 64 PAD); C8 (le_bytes_to_word b3); C8 (le_bytes_to_word b4)]).
    { eapply rw_cells_reshape; [exact HU| cbn; repeat split; reflexivity|]. cbn [cells_bytes cbytes app].
      rewrite (le8_le_bytes_to_word b3 L3), (le8_le_bytes_to_word b4 L4), (le4_of_bytes b2 L2). reflexivity. }
    unfold x509_get_uid_stmt in UID.
    eapply evt_cut.
    { eapply (UID x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 _ _ _ _ x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP UIDA P END BUF LO N bs);
        rewrite ?HSP, <- ?HBL; first [eassumption | reflexivity | lia]. }
    clear UID. intros ms' POST. unfold x509_get_uid_post in POST. rewrite ?HSP in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & tg & ln & qq & -> & MU & WM & MI' & -> & Hr & HPP' & HU2 & ST' & Hp').
    apply evt_done.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sum_getdatesP_MR : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PAL,$23.Plo,$2.PTOP,$2.POPS,(24.P,P,(2<.&40.)(2=.(2<.&8.))Sp)PLAWS,(24.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PPROPS,(24.P,(24.$2.)Sp)PLB0,(24.(1.$2.$2.))PHP,P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,$2>.SpPCW,P,(24.(1.$2.$2.))P,$2.SpPLH,(24.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PHRS,$2?.PTGT,P,$2>.P,$30.SpPCS,P,$2.SpP,(25.$26.VL,R>.)(31.$26.R>.(0.$2.R<.(0.$2.(32.VL,)(0.$2.(28.VL,)(0.$2.(33.VL,)(0.$2.(34.VL,)(0.$2.(35.VL,)(0.$2.R=.(5.$2.))))))))R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.(29.R?.))")
(* [comment removed for export] *).
  Proof. intros. apply summary_okG_MR. apply apply_summary_soundG. apply sum_getdatesP_valid. assumption. Qed.
  Lemma sum_getuidP_MR : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PAL,$23.Plo,$2.PTOP,$2.POPS,(24.P,P,(2<.&40.)(2=.(2<.&8.))Sp)PLAWS,(24.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PPROPS,(24.P,(24.$2.)Sp)PLB0,(24.(1.$2.$2.))PHP,P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,$2>.SpPCW,P,(24.(1.$2.$2.))P,$2.SpPLH,(24.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PHRS,$2?.PTGT,P,$2>.P,$30.SpPCS,P,$2.SpP,(2:.$26.VL,R>.)(31.$26.R>.(0.$2.R<.(0.$2.(32.VL,)(0.$2.(28.VL,)(0.$2.(33.VL,)(0.$2.(34.VL,)(0.$2.(35.VL,)(0.$2.R=.(5.$2.))))))))R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.(2;.R?.))")
(* [comment removed for export] *).
  Proof. intros. apply summary_okG_MR. apply apply_summary_soundG. apply sum_getuidP_valid. assumption. Qed.
End Valid.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PkParse.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable PK : pk_class usegs.
  Variable SI : sinv L.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.

  (* [comment removed for export] *)
  Definition lawPXS : list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "LLB,(24.(1.$2.$2.))Lsp,$2.LX,(24.(1.$2.$2.))Lm,P,(2<.&40.)(2=.(2<.&8.))Lm',P,(2<.&40.)(2=.(2<.&8.))(36.(37.$26.VL,R5.R4.(38.(1.$2.$2.)R3.(39.VL,VSI,))R2.R1.)(36.(3:.(28.VL,)R4.)(3;.(39.VL,VSI,)R5.)))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308579027.2100000FS1L3DHI2sp1x3HSP2Hs2H0". (* [comment removed for export] *)
  Lemma lawPXS_ok : hlaw_ok usegs lawPXS.
  Proof.
    intros LB sp X m1 m2 x (H & HSP & HAV) HR HO Hc. apply H; [exact HR| |].
    - destruct Hc as [Hs|Hb]; [left; exact Hs| right; right; exact Hb].
    - apply outside_app_intro; [exact HO|]. destruct (outside_dec (si_fp SI) x) as [Y|NO]; [exact Y| exfalso].
      destruct Hc as [Hs|(b & Hb & Hr)].
      + pose proof (si_below L SI x NO). lia.
      + apply NO. eapply (fp_avoids_outside (si_fp SI) LB b x HAV Hb). exact Hr.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41625301678.2500000:S1b1k1x2Hx". (* [comment removed for export] *)
  Lemma hcliS_block : forall LB smax b k, In (b, k) LB -> lx_hcli usegs LB lawPXS smax b k.
  Proof.
    intros LB smax b k Hin LB' sp X m1 m2 x HX _ (H & HSP & HAV) Hx HR HO. apply H; [exact HR| |].
    - right; right. exists (b, k). split; [apply HX; exact Hin| cbn; lia].
    - apply outside_app_intro; [exact HO|]. eapply (fp_avoids_outside (si_fp SI) LB' (b, k) x HAV); [apply HX; exact Hin| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L43982016238.11L59310683405.1000000800DS1L1a2HaS1L1a3Hiv2Ha". (* [comment removed for export] *)
  Lemma si_box : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Pm,P,(2<.&40.)(2=.(2<.&8.))P,(3<.VL,VSI,R1.)(3=.$26.$3>.L,$2.$3?.(3<.VL,VSI,)(0.(1.$2.$2.)(4.$2.$2.=(40.VL,))(0.(1.$2.$2.)(4.$2.$2.(41.VL,)+10000000000000000.)(5.(1.$2.$2.))))(5.$42.)R2.)")
(* [comment removed for export] *).
  Proof.
    intros m SP0.
    apply (lx_opq_intro usegs lx_no_layout (fun _ => True) (si_P SI) (fun a => a < hl_data_lo L \/ hl_data_hi L <= a)); [exact SP0| | | intros lo hi c [] ].
    - intros W m1 m2 H1 MU WM HW. apply (si_munch_offdata L SI W m1 m2 H1 MU).
      intros a Ha _. clear - HW Ha. induction HW as [|[u v] W' Hiv HW' IH]; cbn [outside]; [exact I|].
      split; [| exact IH]. intros Hin. cbn [fst snd] in Hiv. specialize (Hiv a Hin). lia.
    - intros lo hi a [E|[E|[]]] Ha; injection E as <- <-; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L43982016238.11L59310683405.1000000800DS1L1a2HaS1L1a3Hiv2Ha". (* [comment removed for export] *)
  Lemma so_box : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Pm,P,(2<.&40.)(2=.(2<.&8.))P,(43.$26.VL,R1.)(3=.$26.$3>.L,$2.$3?.(43.$26.VL,)(0.(1.$2.$2.)(4.$2.$2.=(40.VL,))(0.(1.$2.$2.)(4.$2.$2.(41.VL,)+10000000000000000.)(5.(1.$2.$2.))))(5.$42.)R2.)")
(* [comment removed for export] *).
  Proof.
    intros m SO.
    apply (lx_opq_intro usegs lx_no_layout (fun _ => True) (statics_ok usegs L) (fun a => a < hl_data_lo L \/ hl_data_hi L <= a)); [exact SO| | | intros lo hi c [] ].
    - intros W m1 m2 H1 MU WM HW. apply (statics_ok_munch usegs L W m1 m2 H1 MU).
      intros a Ha _. clear - HW Ha. induction HW as [|[u v] W' Hiv HW' IH]; cbn [outside]; [exact I|].
      split; [| exact IH]. intros Hin. cbn [fst snd] in Hiv. specialize (Hiv a Hin). lia.
    - intros lo hi a [E|[E|[]]] Ha; injection E as <- <-; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition blkP (LB0 : list (Z * Z)) (vs : list Z) : Prop := match vs with [b; k] => In (b, k) LB0 | _ => True end.
  Lemma blk_block : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "PLB,(24.(1.$2.$2.))Plo,$2.PTOP,$2.Pb,$2.Pk,$2.P,(44.(1.$2.$2.)(4.$2.$2.R2.R1.)R5.)(45.(0.Pvs,(24.$2.)Sp(46.VL,R6.)(0.Pvs,(24.$2.)Sp(47.VL,R6.R5.R4.)(0.Pvs,(24.$2.)Sp(48.VL,R6.R5.)(0.Pvs,(24.$2.)Sp(49.R6.)(5.Pvs,(24.$2.)Sp)))))#3.(0.$2.R3.(0.$2.R2.(5.$2.))))")
(* [comment removed for export] *).
  Proof. intros LB lo TOP b k H. exact H. Qed.

  (* [comment removed for export] *)
  Definition RpkP : hres := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Lblo,(24.(1.$2.$2.))Lbln,(24.(1.$2.$2.))Lvs,(24.$2.)Lm,P,(2<.&40.)(2=.(2<.&8.))(4:.(24.$4;.)Lowned,(24.$4;.)(36.(4<.(24.(1.$2.$2.))R4.(38.$4;.R1.R5.))(36.Pb,$4;.P,(44.$4;.R1.R2.)PB,$2.Pk,$2.P,(44.(1.$2.$2.)(4.$2.$2.R2.R1.)R9.)(4=.(3:.(4>.(4?.$2.$2.R5.)(50.$2.$2.R5.))R3.)(3:.(4>.R3.R2.)(4?.$2.$2.R5.)))(36.(51.(1.$2.$2.)Lb,(1.$2.$2.)(52.VL,(4?.$2.$2.R1.)(50.$2.$2.R1.))R1.)(36.(53.$26.VPK,R2.R4.(54.$2.#0.R3.=)(54.$2.#1.R3.=)(54.$2.#2.R3.=)R1.)P,(55.(4<.$2.(54.$2.#3.R3.=)=))(36.(4<.$2.(54.$2.#1.R4.=)=)(36.(4<.$2.(54.$2.#2.R4.=)=)(4<.(24.$4;.)R2.(5.$4;.)))))))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L56763565957.28L59314873579.35L59314938599.31L59315317366.3100000G00Y01301GS1L4ACH01a1b2Hr3HA03HACS1a1b2Hr1B1k3Hr'1HS1L4DIM14DIM21a1b2Hr3HAI1DS1L3TOP1a1b2Hr3HAC1S". (* [comment removed for export] *)
  Lemma RpkP_ok : forall TOP, hres_ok usegs (cwP L TOP) RpkP.
  Proof.
    intros TOP blo bln vs m1 m2 (owned & -> & HAP & HBR & HREP & HR0). intros.
    lazymatch goal with H : (forall x : Z, _ -> in_block _ x -> _ -> _) |- _ => rename H into AG end.
    lazymatch goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    exists owned. split; [reflexivity|]. split; [exact HAP|]. split; [exact HBR|]. split; [| exact HR0].
    pose proof (@alloc_ceiling_lo L) as ACL0. pose proof (@alloc_ceiling_hi L) as ACH0.
    eapply (pk_rep_frame usegs PK); [exact HREP| exact MI2| intros b Hb; apply in_or_app; left; exact Hb|].
    intros a (b & Hb & Hr). rewrite List.Forall_forall in HBR. destruct (HBR b Hb) as (HA0 & _ & _ & HAC & HAI).
    assert (AR : 0 <= a < 2 ^ 64) by lia.
    assert (IB : in_block (owned ++ blo) a) by (exists b; split; [apply in_or_app; left; exact Hb| exact Hr]).
    assert (NCW : ~ cwP L TOP blo a).
    { intros [S|[(D & _)|(bk & Hbk & Hr')]]; [lia| lia|]. destruct bk as [B k]. cbn in Hr'. pose proof (HAP b Hb B k Hbk). lia. }
    exact (proj1 (AG a AR IB NCW)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PkParse.
(* [comment removed for export] *)
Notation OPS2 L SI := [statics_ok usegs L; @si_P L SI].
Notation LH3 L SI := [lawP L; lawPX L; lawPXS L SI].
Notation PROPS4 L LB0 lo TOP := [objP L LB0; cwoP L LB0 lo TOP; croP L LB0 lo; blkP LB0].
Notation HRS2 L PK := [RnameP L; RpkP L PK].

(* [comment removed for export] *)
Definition havoc16' : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(0.(1.$2.$3.)(4.$2.$3.+:.^10.)(0.(1.$2.$3.)(4.$2.$3.+5.^11.)(0.(1.$2.$3.)(4.$2.$3.+6.^12.)(0.(1.$2.$3.)(4.$2.$3.+7.^13.)(0.(1.$2.$3.)(4.$2.$3.+;.^14.)(0.(1.$2.$3.)(4.$2.$3.+<.^15.)(0.(1.$2.$3.)(4.$2.$3.+=.^16.)(0.(1.$2.$3.)(4.$2.$3.+>.^17.)(0.(1.$2.$3.)(4.$2.$3.+?.^18.)(0.(1.$2.$3.)(4.$2.$3.+10.^19.)(0.(1.$2.$3.)(4.$2.$3.+11.^1:.)(0.(1.$2.$3.)(4.$2.$3.+1<.^1;.)(0.(1.$2.$3.)(4.$2.$3.+1=.^1<.)(0.(1.$2.$3.)(4.$2.$3.+1>.^1=.)(0.(1.$2.$3.)(4.$2.$3.+1?.^1>.)(5.(1.$2.$3.)))))))))))))))))")
(* [comment removed for export] *).
Definition HC_pkparseP : heapcall := HCR 2%nat 4%positive [] None BEOpq None [(1%nat, [q 3; q 32; q 33; q 16])].
Definition SUM_pkparseP (pc : Z) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(56.O1.$7.#?.#12.#1.(0.(1.$2.$3.)(4.$2.$3.+:.^1.)(0.(1.$2.$3.)(4.$2.$3.+;.^2.)(0.(1.$2.$3.)(4.$2.$3.+<.^3.)(0.(1.$2.$3.)(4.$2.$3.+2.^4.)(0.(1.$2.$3.)(4.$2.$3.+4.^5.)(5.(1.$2.$3.)))))))(0.(1.$3.$8.)(4.$3.$8.^6.#0.)(0.(1.$3.$8.)(4.$3.$8.^7.#1.)(0.(1.$3.$8.)(4.$3.$8.^8.#2.)(0.(1.$3.$8.)(4.$3.$8.^9.#3.)(0.(1.$3.$8.)(4.$3.$8.^:.#4.)(0.(1.$3.$8.)(4.$3.$8.^;.#5.)(0.(1.$3.$8.)(4.$3.$8.^<.#6.)(5.(1.$3.$8.)))))))))(9.$3.)(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^=.))(5.$=.)))(0.$:.(;.(<.^3.)(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(5.$=.))))(5.$:.)))(10.(1.$3.$3.)(4.$3.$3.^<.^4.))(0.(1.(1.$3.$3.)$3.)(4.(1.$3.$3.)$3.(4.$3.$3.^>.^?.)^1.)(5.(1.(1.$3.$3.)$3.)))(5.$:.)(0.$11.(12.(<.^5.)(<.^9.))(0.$11.(15.(<.^>.)(<.^=.))(0.$11.(15.(<.^=.)(<.^2.))(0.$11.(15.(<.^2.)(13.(<.^>.)(<.^?.)))(0.$11.(16.(13.(<.^>.)(<.^?.))(14.(17.+2.+3?.)))(0.$11.(16.(14.=)(<.^>.))(0.$11.(19.(1:.^1.)&3.)(0.$11.(19.(1:.^3.)&3.)(0.$11.(15.(<.^4.)(<.^1.))(0.$11.(15.(13.(<.^1.)(14.+8.))(<.^6.))(0.$11.(15.(<.^4.)(<.^3.))(0.$11.(15.(13.(<.^3.)(14.+10.))(<.^6.))(0.$11.(18.(<.^1.)(14.+8.)(<.^3.)(14.+10.))(0.$11.(15.(<.^8.)(<.^<.))(0.$11.(15.(<.^<.)(13.(13.(<.^4.)(1;.-1.(14.$57.)))(1;.-1.(<.^7.))))(0.$11.(19.(1:.^4.)&4.)(0.$11.(15.(<.^4.)(<.^6.))(0.$11.(16.(<.^4.)(14.(17.+2.+40.)))(0.$11.(18.(<.^1.)(14.+8.)(<.^>.)(<.^?.))(0.$11.(18.(<.^3.)(14.+10.)(<.^>.)(<.^?.))(0.$11.(16.(14.=)(<.^1.))(0.$11.(16.(14.=)(<.^3.))(0.$11.(1=.(13.(<.^1.)(14.+8.))(<.^<.)(<.^4.)(<.^1.))(0.$11.(1=.(13.(<.^3.)(14.+10.))(<.^<.)(<.^4.)(<.^3.))(0.$11.(1=.(13.(<.^>.)(<.^?.))(<.^<.)(<.^4.)(<.^>.))(0.$11.(58.#1.(0.$1>.(<.^1.)(0.$1>.(14.+8.)(5.$1>.))))(0.$11.(58.#1.(0.$1>.(<.^3.)(0.$1>.(14.+10.)(5.$1>.))))(0.$11.(58.#2.(0.$1>.(<.^>.)(0.$1>.(<.^?.)(5.$1>.))))(0.$11.(58.#3.(0.$1>.(<.^>.)(0.$1>.(<.^?.)(5.$1>.))))(5.$11.))))))))))))))))))))))))))))))(0.(1.$1>.$1>.)(4.$1>.$1>.(<.^1.)(13.(<.^1.)(14.+8.)))(0.(1.$1>.$1>.)(4.$1>.$1>.(<.^3.)(13.(<.^3.)(14.+10.)))(5.(1.$1>.$1>.))))$59.(0.$:.(20.(<.^<.)(<.^4.))(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^1?.))(5.$=.)))(0.$:.(;.(<.^3.)(0.$=.(>.&8.(<.^20.))(0.$=.(>.&8.(<.^21.))(5.$=.))))(5.$:.))))(0.$11.(16.(14.(5:.(17.+2.+1?.)))(<.^10.))(0.$11.(15.(<.^10.)(14.=))(0.$11.(15.(<.^=.)(<.^1?.))(0.$11.(15.(<.^1?.)(<.^2.))(5.$11.)))))(0.$8.#0.(0.$8.#1.(5.$8.)))(9.$8.)(10.$5;.$5<.))")
(* [comment removed for export] *).

Section PkParseValid.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable PK : pk_class usegs.
  Variable SI : sinv L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L14850789069.148L15648069410.109L20630334781.148L21313719894.148L22371965159.148L23767186630.108L25344871455.109L25638568605.109L28632459695.148L30035450845.108L3106860245.148 L35074957040.148L36926659245.109L44306624557.109L57051596348.148L58972692712.109L59027649715.109L59773154551.109L61472138903.109L61490180196.148L66426478413.148L68314649325.10900000O00P01701801_02W02X04604704U04V04W05406_07W08_08`08a0:J0:i0:j0<6S2PP3PKA2SP2bs3AL13AL23SPA1r2HrFS2PP3END3PKA2SP1P2bs3AL13AL23SPA2p'3Hp'FS2PP3END3PKA2SP1P2bs3AL13AL23SPA2p'3Hp'S1L3HLS2lo2PP3PKA2SP2bs3AL13AL23SLO3ACL3SPA3NZ13NZ24ACL0FS1L3HLS2lo2PP3PKA2SP3BUF4BLEN2bs3HBL3AL13AL23SPP3SPK2D13SLO3ACL3SPA2D22D33NZ13NZ23DS23DS14ACL0FS2PP3PKA2SP2bs3AL13AL23SPA3SPBFFS2PP3PKA2SP2bs3AL13AL22D13SPAS1L3HLS2lo2PP3END3PKA2SP1P3BUF4BLEN2bs3HBL2B12B22B33AL13AL23SPP3SPK3SLO3ACL3SPA2D23NZ13NZ23DS33DS23DS14ACL0S1L3HLS2lo2PP3PKA2SP2bs3AL13AL23SLO3ACL3SPA3NZ13NZ24ACL0S1L3HLS2lo2PP3PKA2SP3BUF4BLEN2bs3HBL2B43AL13AL23SLO3ACL3SPA3NZ13NZ24ACL0FFS1L3HLS2lo2PP3END3PKA2SP1P3BUF4BLEN2bs3HBL2B12B22B33AL13AL23SPP3SPK2D13SLO3ACL3SPA2D22D33NZ13NZ23DS24ACL0S2PP3PKA2SP2bs3AL13AL23SPA1r2HrFS1L3HLS2lo2PP3END3PKA2SP3BUF4BLEN2bs3HBL2B33AL13AL23SLO3ACL3SPA3NZ13NZ24ACL0". (* [comment removed for export] *)
  Lemma sum_pkparseP_valid : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PQ,P,$5=.SpPLB0,(24.(1.$2.$2.))Plo,$2.PTOP,$2.PMO0,$2>.PAL,$23.PLAWS,(24.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PCS,P,$2.SpPOPSX,(24.P,P,(2<.&40.)(2=.(2<.&8.))Sp)PGX,(24.$2.)PPX,(24.Pvs,(24.$2.)Sp)PLX,(24.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PR0,$5>.PHX,(24.$5>.)P,(5?.$26.VL,VHI,VPK,VSI,R?.)(60.$26.R:.(38.$2.(0.$2.R<.(0.$2.(32.VL,)(0.$2.(28.VL,)(0.$2.(33.VL,)(0.$2.(34.VL,)(0.$2.(35.VL,)(0.$2.R=.(5.$2.))))))))R6.)(0.Pm,P,(2<.&40.)(2=.(2<.&8.))Sp(43.$26.VL,)(0.P,P,(2<.&40.)(2=.(2<.&8.))Sp(3<.VL,VSI,)R7.))R9.(38.Pvs,(24.$2.)Sp(0.Pvs,(24.$2.)Sp(46.VL,R>.)(0.Pvs,(24.$2.)Sp(47.VL,R>.R=.R<.)(0.Pvs,(24.$2.)Sp(48.VL,R>.R=.)(0.Pvs,(24.$2.)Sp(61.R>.)(5.Pvs,(24.$2.)Sp)))))R5.)R>.(62.VL,VHI,R<.R;.)(63.VL,R<.)(38.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(64.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(65.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(66.VL,VSI,)(5.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp))))R4.)(0.$5>.R3.(0.$5>.(67.VL,VPK,)R2.))(68.$26.R?.)(69.R10.)$5<.R8.)")
(* [comment removed for export] *).
  Proof.
    intros pc Q LB0 lo TOP MO0 AL LAWS CS OPSX GX PX LX R0 HX PKP. cbn [app]. split; [reflexivity|]. unfold SUM_pkparseP, HC_pkparseP, havoc16', q. lx_sum_unfold.
    intros PP END PKA SP TPV TOP' HLS' ACE HLTP IMGLO IMGHI LO P BUF BLEN.
    intros bs.
    intros F fc m mo LB.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros _ _ MI G0 G1 G2 G3 G4 G5 G6 R10 R11 R12 R2 R4 ST HPP HPKA [HBUF HBL].
    intros TP B1 B2 B3 B4 NZB AL1 AL2 SPP PPT SPK PKT D1 ACL SLO SPA HTOP SPB D2 D3 NZ1 NZ2 DS1 DS2 DS3 CW1 CW2 CR3 BK3.
    intros SOK SIP EXT (h & HH & HT & MF) _ K1 _.
    unfold tgt_aevtM. intros MK. subst x10 x11 x12 x2 x4. subst TOP' HLS' ACE HLTP IMGLO IMGHI LO TPV.
    cbn [cwoP croP blkP] in CW1, CW2, CR3, BK3.
    pose proof (@alloc_ceiling_lo L) as ACL0.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64, PK_PARSE_STACK in *; lia).
    unfold pk_parse_subpubkey_stmt in PKP.
    eapply aevtM_cut.
    { eapply PKP with (lo := lo) (bs := bs) (PP := PP) (PKA := PKA) (P := P) (END := END) (BUF := BUF) (h := h) (LB := LB);
        rewrite ?HSP, ?HT, <- ?HBL; try reflexivity; try eassumption; try (unfold PK_PARSE_STACK in *; lia).
      all: rewrite ?HBL; first [ eapply client_wrange_ext; [eassumption| exact EXT] | eapply client_range_ext; [exact CR3| exact EXT] | apply EXT; exact BK3 | exact SW ]. }
    clear PKP. intros ms' mo2 PO. unfold pk_parse_subpubkey_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & h' & r & p' & info & ctx & owned & E & PO).
    injection E; intros <- ->. rewrite ?HSP in PO.
    destruct PO as (-> & Hr & MI' & SO' & SI' & ST' & MF' & HT' & HPP' & Hp' & HPKA' & HREP & HR0 & HH' & HPX).
    lx_aevtM_zregs.
    destruct (heap_blocks _ _ HI _ _ _ _ HH') as [HBR HAP]. rewrite Forall_app in HBR. destruct HBR as [HBRo HBRl].
    eapply (K1 r _ _ _ _ _ _ _ _ _ _ _ _ _ _ p' info ctx _ _ (owned ++ LB));
      try eassumption; try reflexivity; try exact I; try lia; try exact (heap_mok _ _ HI _ _ _ _ HH').
    - (* [comment removed for export] *)
      split; [| split; [apply RpkP_ok; [exact DIM1| exact DIM2]| split; [apply cwP_blk| split; [constructor| split; [exact EXT| intros b Hb; apply in_or_app; right; exact Hb]]]]].
      exists owned. cbn [nth]. split; [reflexivity|]. split; [| split; [exact HBRo| split; [exact HREP| exact HR0]]].
      intros b Hb B k HBk.
      (* [comment removed for export] *)
      clear - HAP Hb HBk. induction owned as [|[a n] owned IH]; [destruct Hb|]. cbn [app blocks_apart] in HAP. destruct HAP as [HA HAP].
      destruct Hb as [<-|Hb]; [cbn [fst snd]; apply (HA B k); apply in_or_app; right; exact HBk| exact (IH HAP Hb)].
    - (* [comment removed for export] *)
      exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
    - (* [comment removed for export] *) intros b Hb. apply in_or_app. right. exact Hb.
    - (* [comment removed for export] *)
      split; [| split; [unfold PK_PARSE_STACK in *; lia| eapply (si_fp_avoids_HEAP usegs L SI HI); [exact HH| exact DIM1| exact DIM2]]].
      exact HPX.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma SUMS_pkP_ok : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PQ,P,$5=.SpPLB0,(24.(1.$2.$2.))Plo,$2.PTOP,$2.PMO0,$2>.P,(5?.$26.VL,VHI,VPK,VSI,R6.)(51.$6:.(31.$26.$3>.(0.$2.R3.(0.$2.(32.VL,)(0.$2.(28.VL,)(0.$2.(33.VL,)(0.$2.(34.VL,)(0.$2.(35.VL,)(0.$2.R4.(5.$2.))))))))(0.Pm,P,(2<.&40.)(2=.(2<.&8.))Sp(43.$26.VL,)(0.P,P,(2<.&40.)(2=.(2<.&8.))Sp(3<.VL,VSI,)(5.P,P,(2<.&40.)(2=.(2<.&8.))Sp)))(5.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)(0.Pvs,(24.$2.)Sp(46.VL,R5.)(0.Pvs,(24.$2.)Sp(47.VL,R5.R4.R3.)(0.Pvs,(24.$2.)Sp(48.VL,R5.R4.)(0.Pvs,(24.$2.)Sp(61.R5.)(5.Pvs,(24.$2.)Sp)))))R5.(62.VL,VHI,R3.R2.)(63.VL,R3.)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(64.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(65.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(66.VL,VSI,)(5.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp))))(0.$5>.(6;.VL,)(0.$5>.(67.VL,VPK,)(5.$5>.)))(68.$26.R6.)L,$2.$3?.)(0.$6:.(69.R7.)(5.$6:.)))")
(* [comment removed for export] *).
  Proof. intros. constructor; [| constructor]. eapply apply_summary_soundMR. apply (sum_pkparseP_valid pc Q LB0 lo TOP MO0 _ [] _ [] [] [] [] _ []). assumption. Qed.
  Lemma heapkit_introS : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ph,(6<.$26.VL,VHI,)PLB,(24.$4;.)Pm,P,(2<.&40.)(2=.(2<.&8.))Pmo,$2>.POK,(24.$42.)P,(6=.$26.VL,VHI,R5.R4.R3.R2.)P,(51.(1.$2.$2.)Liv,(1.$2.$2.)Px,$2.P,(36.(3:.(4?.$2.$2.R2.)R1.)(6>.R1.(50.$2.$2.R2.)))PLB',(24.$4;.)P,Pb,$4;.P,(44.$4;.R1.R:.)(44.$4;.R2.R3.)(63.VL,(6?.$26.VL,VHI,R;.)R2.R4.)R2.)(70.$26.(62.VL,VHI,(6?.$26.VL,VHI,R7.)R4.)(63.VL,(6?.$26.VL,VHI,R7.))(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(64.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(65.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(66.VL,VSI,)(5.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp))))R6.R6.R3.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo OK HH HOK. destruct (heapkit_intro L HI h LB m mo OK HH HOK) as [A [B [C [D _]]]].
    split; [exact A| split; [exact B| split; [exact C| split; [exact D|]]]].
    constructor; [apply lawP_ok| constructor; [apply lawPX_ok| constructor; [apply lawPXS_ok; exact DHI| constructor]]].
  Qed.
End PkParseValid.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CrtExt.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable PK : pk_class usegs.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.

  Definition RextP : hres := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Lblo,(24.(1.$2.$2.))Lbln,(24.(1.$2.$2.))Lvs,(24.$2.)Lm,P,(2<.&40.)(2=.(2<.&8.))(4:.$71.Leo,$71.(4:.(24.$4;.)LLBx,(24.$4;.)(36.(4<.(24.(1.$2.$2.))R5.(38.$4;.R1.R6.))(36.(72.$4;.R1.(73.R2.))(36.Pb,$4;.P,(44.$4;.R1.R2.)PB,$2.Pk,$2.P,(44.(1.$2.$2.)(4.$2.$2.R2.R1.)R:.)(4=.(3:.(4>.(4?.$2.$2.R5.)(50.$2.$2.R5.))R3.)(3:.(4>.R3.R2.)(4?.$2.$2.R5.)))(36.(51.(1.$2.$2.)Lb,(1.$2.$2.)(52.VL,(4?.$2.$2.R1.)(50.$2.$2.R1.))R1.)(36.(74.$26.R3.R5.R2.)(36.(4<.$2.(75.R2.)(54.$2.#0.R4.=))(36.(4<.$2.(76.R2.)(54.$2.#1.R4.=))(36.(4<.$2.(77.R2.)(54.$2.#2.R4.=))(4<.$2.(78.R2.)(54.$2.#3.R4.=))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L39056721409.32L59314873579.37L59314938599.33L59315317366.3300000;00O00l01CS1x2cs1y2HyS1x2cs1y2Hy1b1k2Hr1HS1L4DIM14DIM21x2cs1y2Hy3HAI1DS1L3TOP1x2cs1y2Hy3HAC1S". (* [comment removed for export] *)
  Lemma seq_chain_agree : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Pm1,Px,(2<.&40.)(2=.(2<.&8.))Pm2,Px,(2<.&40.)(2=.(2<.&8.))Pbln,(24.$4;.)Pblo,(24.$4;.)PLBx,(24.$4;.)Peo,$71.PTOP,$2.Pa,$2.Pnodes,(24.$2.)P,(4<.(24.$4;.)R7.(38.$4;.R5.R6.))P,(72.$4;.R6.(73.R5.))P,Pb,$4;.P,(44.$4;.R1.R8.)PB,$2.Pk,$2.P,(44.(1.$2.$2.)(4.$2.$2.R2.R1.)R<.)(4=.(3:.(4>.(4?.$2.$2.R5.)(50.$2.$2.R5.))R3.)(3:.(4>.R3.R2.)(4?.$2.$2.R5.)))P,(51.(1.$2.$2.)Lb,(1.$2.$2.)(52.VL,(4?.$2.$2.R1.)(50.$2.$2.R1.))R8.)P,Px,$2.P,(44.$2.R1.R6.)(44.(1.$2.$2.)(4.$2.$2.R2.$79.)(73.R:.))P,Px,$2.P,(36.(3:.=R1.)(6>.R1.(17.+2.+40.)))P,(7:.R>.R2.)P,(55.(63.VL,R;.R>.R3.))(36.(4<.(2=.(2<.&8.))A1.R11.(7;.R4.)A1.R12.(7;.R4.))P,(55.(4<.(2=.(2<.&8.))(7<.$26.R12.(7;.R4.))(9.(2<.&8.))))(55.(4<.(2=.(2<.&8.))(7<.$26.R12.(7;.R5.))(9.(2<.&8.)))))P,(7=.$26.L,(24.$7>.)$3?.R?.R=.R8.R7.)(7=.$26.L,(24.$7>.)$3?.R?.R>.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros m1 m2 bln blo LBx eo TOP a nodes -> PERM HAP HBR HNODES AG HCH. pose proof (@alloc_ceiling_lo L) as ACL0.
    eapply chain_mem; [exact HCH| intros x Hx; exact (chain_nodes_in _ _ _ _ _ _ _ _ HCH x Hx)|].
    intros x cs Hx HC HSZ. eapply rw_cells_agree; [exact HC|]. rewrite HSZ. change SEQ_SIZE with 32. intros y Hy HRy.
    assert (HIN : In (x, 32) LBx) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact (HNODES x Hx)]).
    rewrite List.Forall_forall in HBR. destruct (HBR _ HIN) as (HA0 & _ & _ & HAC & HAI). cbn [fst snd] in HA0, HAC, HAI.
    apply AG; [exact HRy| exists (x, 32); split; [apply in_or_app; left; exact HIN| cbn; lia]|].
    intros [S|[(D & _)|(bk & Hbk & Hr)]]; [lia| lia|]. destruct bk as [b k]. cbn in Hr. pose proof (HAP _ HIN b k Hbk). cbn [fst snd] in *. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma RextP_ok : forall TOP, hres_ok usegs (cwP L TOP) RextP.
  Proof.
    intros TOP blo bln vs m1 m2 (eo & LBx & E & PERM & HAP & HBR & (C1 & C2 & C3 & C4) & HN). intros.
    lazymatch goal with H : (forall x : Z, _ -> in_block _ x -> _ -> _) |- _ => rename H into AG end.
    exists eo, LBx. split; [exact E|]. split; [exact PERM|]. split; [exact HAP|]. split; [exact HBR|]. split; [| exact HN].
    unfold ext_blocks in PERM.
    split; [| split; [| split]].
    - eapply (seq_chain_agree m1 m2 bln blo LBx eo TOP); try eassumption. intros x Hx. unfold ext_blocks. rewrite !in_app_iff. right; left. apply in_map_iff. exists x. auto.
    - eapply (seq_chain_agree m1 m2 bln blo LBx eo TOP); try eassumption. intros x Hx. unfold ext_blocks. rewrite !in_app_iff. right; right; right. apply in_map_iff. exists x. auto.
    - eapply (seq_chain_agree m1 m2 bln blo LBx eo TOP); try eassumption. intros x Hx. unfold ext_blocks. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists x. auto.
    - eapply (seq_chain_agree m1 m2 bln blo LBx eo TOP); try eassumption. intros x Hx. unfold ext_blocks. rewrite !in_app_iff. left. apply in_map_iff. exists x. auto.
  Qed.
End CrtExt.
Notation HRS3 L PK := [RnameP L; RpkP L PK; RextP L].

(* [comment removed for export] *)
Definition havoc17 : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(0.(1.$2.$3.)(4.$2.$3.+:.^11.)(0.(1.$2.$3.)(4.$2.$3.+5.^12.)(0.(1.$2.$3.)(4.$2.$3.+6.^13.)(0.(1.$2.$3.)(4.$2.$3.+7.^14.)(0.(1.$2.$3.)(4.$2.$3.+;.^15.)(0.(1.$2.$3.)(4.$2.$3.+<.^16.)(0.(1.$2.$3.)(4.$2.$3.+=.^17.)(0.(1.$2.$3.)(4.$2.$3.+>.^18.)(0.(1.$2.$3.)(4.$2.$3.+?.^19.)(0.(1.$2.$3.)(4.$2.$3.+10.^1:.)(0.(1.$2.$3.)(4.$2.$3.+11.^1;.)(0.(1.$2.$3.)(4.$2.$3.+1<.^1<.)(0.(1.$2.$3.)(4.$2.$3.+1=.^1=.)(0.(1.$2.$3.)(4.$2.$3.+1>.^1>.)(0.(1.$2.$3.)(4.$2.$3.+1?.^1?.)(5.(1.$2.$3.)))))))))))))))))")
(* [comment removed for export] *).
Definition HC_crtextP : heapcall := HCR 1%nat 5%positive [] None BEOpq None [(2%nat, [q 39; q 49; q 59; q 65])].
Definition SUM_crtextP (pc : Z) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(56.O1.$7.#10.#32.#1.(0.(1.$2.$3.)(4.$2.$3.+:.^1.)(0.(1.$2.$3.)(4.$2.$3.+;.^2.)(0.(1.$2.$3.)(4.$2.$3.+<.^3.)(0.(1.$2.$3.)(4.$2.$3.+=.^4.)(0.(1.$2.$3.)(4.$2.$3.+2.^5.)(0.(1.$2.$3.)(4.$2.$3.+4.^6.)(5.(1.$2.$3.))))))))(0.(1.$3.$8.)(4.$3.$8.^7.#0.)(0.(1.$3.$8.)(4.$3.$8.^8.#1.)(0.(1.$3.$8.)(4.$3.$8.^9.#2.)(0.(1.$3.$8.)(4.$3.$8.^:.#3.)(0.(1.$3.$8.)(4.$3.$8.^;.#4.)(0.(1.$3.$8.)(4.$3.$8.^<.#5.)(0.(1.$3.$8.)(4.$3.$8.^=.#6.)(5.(1.$3.$8.)))))))))(9.$3.)(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^>.))(5.$=.)))(0.$:.(;.(13.(<.^3.)(14.+1:8.))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(0.$=.(>.&8.(14.=))(5.$=.))))))))))))))))))))))))))))))))))))(5.$:.)))(10.(1.$3.$3.)(4.$3.$3.^=.^5.))(0.(1.(1.$3.$3.)$3.)(4.(1.$3.$3.)$3.(4.$3.$3.^?.^10.)^1.)(5.(1.(1.$3.$3.)$3.)))(5.$:.)(0.$11.(12.(<.^6.)(<.^:.))(0.$11.(12.(<.^4.)(14.=))(0.$11.(15.(<.^?.)(<.^>.))(0.$11.(15.(<.^>.)(<.^2.))(0.$11.(15.(<.^2.)(13.(<.^?.)(<.^10.)))(0.$11.(16.(13.(<.^?.)(<.^10.))(14.(17.+2.+3?.)))(0.$11.(16.(14.=)(<.^?.))(0.$11.(19.(1:.^1.)&3.)(0.$11.(19.(1:.^3.)&3.)(0.$11.(15.(<.^5.)(<.^1.))(0.$11.(15.(13.(<.^1.)(14.+8.))(<.^7.))(0.$11.(15.(<.^5.)(13.(<.^3.)(14.+1:8.)))(0.$11.(15.(13.(<.^3.)(14.+2;8.))(<.^7.))(0.$11.(18.(<.^1.)(14.+8.)(13.(<.^3.)(14.+1:8.))(14.+110.))(0.$11.(15.(<.^9.)(<.^=.))(0.$11.(15.(<.^=.)(13.(13.(<.^5.)(1;.-1.(14.$7?.)))(1;.-1.(<.^8.))))(0.$11.(19.(1:.^5.)&4.)(0.$11.(15.(<.^5.)(<.^7.))(0.$11.(16.(<.^5.)(14.(17.+2.+40.)))(0.$11.(58.#3.(0.$1>.(<.^?.)(0.$1>.(<.^10.)(5.$1>.))))(5.$11.)))))))))))))))))))))(0.(1.$1>.$1>.)(4.$1>.$1>.(<.^1.)(13.(<.^1.)(14.+8.)))(0.(1.$1>.$1>.)(4.$1>.$1>.(13.(<.^3.)(14.+1:8.))(13.(<.^3.)(14.+2;8.)))(5.(1.$1>.$1>.))))$80.(0.$:.(20.(<.^=.)(<.^5.))(0.$:.(;.(<.^1.)(0.$=.(>.&8.(<.^20.))(5.$=.)))(0.$:.(;.(13.(<.^3.)(14.+1:8.))(0.$=.(>.&8.(<.^21.))(0.$=.(>.&8.(<.^22.))(0.$=.(>.&8.(<.^23.))(0.$=.(>.&8.(<.^24.))(0.$=.(>.&8.(<.^25.))(0.$=.(>.&8.(<.^26.))(0.$=.(>.&8.(<.^27.))(0.$=.(>.&8.(<.^28.))(0.$=.(>.&8.(<.^29.))(0.$=.(>.&8.(<.^2:.))(0.$=.(>.&8.(<.^2;.))(0.$=.(>.&8.(<.^2<.))(0.$=.(>.&8.(<.^2=.))(0.$=.(>.&8.(<.^2>.))(0.$=.(>.&8.(<.^2?.))(0.$=.(>.&8.(<.^30.))(0.$=.(>.&8.(<.^31.))(0.$=.(>.&8.(<.^32.))(0.$=.(>.&8.(<.^33.))(0.$=.(>.&8.(<.^34.))(0.$=.(>.&8.(<.^35.))(0.$=.(>.&8.(<.^36.))(0.$=.(>.&8.(<.^37.))(0.$=.(>.&8.(<.^38.))(0.$=.(>.&8.(<.^39.))(0.$=.(>.&8.(<.^3:.))(0.$=.(>.&8.(<.^3;.))(0.$=.(>.&8.(<.^3<.))(0.$=.(>.&8.(<.^3=.))(0.$=.(>.&8.(<.^3>.))(0.$=.(>.&8.(<.^3?.))(0.$=.(>.&8.(<.^40.))(0.$=.(>.&8.(<.^41.))(0.$=.(>.&8.(<.^42.))(5.$=.))))))))))))))))))))))))))))))))))))(5.$:.))))(0.$11.(16.(14.(5:.(17.+2.+1?.)))(<.^11.))(0.$11.(15.(<.^11.)(14.=))(0.$11.(15.(<.^>.)(<.^20.))(0.$11.(15.(<.^20.)(<.^2.))(5.$11.)))))(0.$8.#0.(5.$8.))(9.$8.)(10.$5;.$81.))")
(* [comment removed for export] *).

Section CrtExtValid.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable PK : pk_class usegs.
  Variable SI : sinv L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.

  (* [comment removed for export] *)
  Definition ext_words (eo : ext_own) (ej : ext_junk) : list cell := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "(38.$7>.(82.#6.(83.O1.))(38.$7>.(0.$7>.(84.(85.&40.(75.O2.)))(5.$7>.))(38.$7>.(82.#9.(86.O1.))(38.$7>.(0.$7>.(84.(85.&40.(76.O2.)))(5.$7>.))(38.$7>.(82.#9.(87.O1.))(38.$7>.(0.$7>.(84.(85.&40.(77.O2.)))(5.$7>.))(38.$7>.(82.#5.(88.O1.))(38.$7>.(0.$7>.(84.(85.&40.(78.O2.)))(5.$7>.))(82.#1.(89.O1.))))))))))")
(* [comment removed for export] *).
  Lemma ext_cells_words : forall m A eo ej, rw_cells usegs m A (ext_cells eo ej) -> rw_cells usegs m A (ext_words eo ej).
  Proof.
    intros m A eo ej H. pose proof H as H0. destruct H as [[WF _] _]. cbn in WF. destruct WF as (L0 & _ & L1 & _ & L2 & _ & L3 & _ & L4 & _).
    eapply rw_cells_reshape; [exact H0| |]; unfold ext_words.
    - rewrite !cells_wf_app. cbn [cells_wf]. repeat split; try exact I; apply wchunks_wf.
    - rewrite !cells_bytes_app. rewrite !wchunks_bytes by (rewrite ?L0, ?L1, ?L2, ?L3, ?L4; reflexivity).
      unfold ext_cells. cbn [cells_bytes cbytes app]. rewrite <- !app_assoc. cbn [app]. rewrite ?app_nil_r. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma words_ext_cells : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Pm,P,(2<.&40.)(2=.(2<.&8.))PA,$2.Peo,$71.Pz0,$2.Pz1,$2.Pz2,$2.Pz3,$2.Pz4,$2.Pz5,$2.Pz7,$2.Pz8,$2.Pz9,$2.Pz10,$2.Pz11,$2.Pz12,$2.Pz13,$2.Pz14,$2.Pz15,$2.Pz17,$2.Pz18,$2.Pz19,$2.Pz20,$2.Pz21,$2.Pz22,$2.Pz23,$2.Pz24,$2.Pz25,$2.Pz27,$2.Pz28,$2.Pz29,$2.Pz30,$2.Pz31,$2.Pz33,$2.P,(8:.$26.R21.R20.(0.$7>.(84.(85.&40.R1>.))(0.$7>.(84.(85.&40.R1=.))(0.$7>.(84.(85.&40.R1<.))(0.$7>.(84.(85.&40.R1;.))(0.$7>.(84.(85.&40.R1:.))(0.$7>.(84.(85.&40.R19.))(0.$7>.(84.(85.&40.(75.R1?.)))(0.$7>.(84.(85.&40.R18.))(0.$7>.(84.(85.&40.R17.))(0.$7>.(84.(85.&40.R16.))(0.$7>.(84.(85.&40.R15.))(0.$7>.(84.(85.&40.R14.))(0.$7>.(84.(85.&40.R13.))(0.$7>.(84.(85.&40.R12.))(0.$7>.(84.(85.&40.R11.))(0.$7>.(84.(85.&40.R10.))(0.$7>.(84.(85.&40.(76.R1?.)))(0.$7>.(84.(85.&40.R?.))(0.$7>.(84.(85.&40.R>.))(0.$7>.(84.(85.&40.R=.))(0.$7>.(84.(85.&40.R<.))(0.$7>.(84.(85.&40.R;.))(0.$7>.(84.(85.&40.R:.))(0.$7>.(84.(85.&40.R9.))(0.$7>.(84.(85.&40.R8.))(0.$7>.(84.(85.&40.R7.))(0.$7>.(84.(85.&40.(77.R1?.)))(0.$7>.(84.(85.&40.R6.))(0.$7>.(84.(85.&40.R5.))(0.$7>.(84.(85.&40.R4.))(0.$7>.(84.(85.&40.R3.))(0.$7>.(84.(85.&40.R2.))(0.$7>.(84.(85.&40.(78.R1?.)))(0.$7>.(84.(85.&40.R1.))(5.$7>.))))))))))))))))))))))))))))))))))))(4:.$8;.Lej,$8;.(8:.$26.R23.R22.(8<.R21.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros. exists (EXJ (le8 (Z_to_bv 64 z0) ++ le8 (Z_to_bv 64 z1) ++ le8 (Z_to_bv 64 z2) ++ le8 (Z_to_bv 64 z3) ++ le8 (Z_to_bv 64 z4) ++ le8 (Z_to_bv 64 z5)) (le8 (Z_to_bv 64 z7) ++ le8 (Z_to_bv 64 z8) ++ le8 (Z_to_bv 64 z9) ++ le8 (Z_to_bv 64 z10) ++ le8 (Z_to_bv 64 z11) ++ le8 (Z_to_bv 64 z12) ++ le8 (Z_to_bv 64 z13) ++ le8 (Z_to_bv 64 z14) ++ le8 (Z_to_bv 64 z15))
                   (le8 (Z_to_bv 64 z17) ++ le8 (Z_to_bv 64 z18) ++ le8 (Z_to_bv 64 z19) ++ le8 (Z_to_bv 64 z20) ++ le8 (Z_to_bv 64 z21) ++ le8 (Z_to_bv 64 z22) ++ le8 (Z_to_bv 64 z23) ++ le8 (Z_to_bv 64 z24) ++ le8 (Z_to_bv 64 z25)) (le8 (Z_to_bv 64 z27) ++ le8 (Z_to_bv 64 z28) ++ le8 (Z_to_bv 64 z29) ++ le8 (Z_to_bv 64 z30) ++ le8 (Z_to_bv 64 z31)) (le8 (Z_to_bv 64 z33))).
    eapply rw_cells_reshape; [eassumption| cbn; repeat split; reflexivity| cbn; reflexivity].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L14850789069.136L20630334781.136L21313719894.136L22371965159.136L23767186630.96 L30035450845.96 L30184552563.136L42105763921.98 L48419202207.136L56492766089.136L58985277009.98 L59760570958.98 L61490180196.136L66426478413.136L6648087627.136 L68302066772.98 00000P01801901a02R03103203V03W04205;05<05\05]05^06kS2PP4CRTV2SP2bs3AL13AL33SPA1r2HrS2PP3END4CRTV2SP1P2bs3AL13AL33SPA2p'3Hp'FS2PP3END4CRTV2SP1P2bs3AL13AL33SPA2p'3Hp'S1L3HLS2lo2PP4CRTV2SP2bs3AL13AL33SLO3ACL3SPA4ACL0S2PP4CRTV2SP2bs3AL13AL33SPA3SPBFS3TOP2PP4CRTV2SP2bs3AL13AL34EXT'3SPAFS2PP4CRTV2SP2bs3AL13AL33SPAS1L3HLS2lo2PP4CRTV2SP3BUF4BLEN2bs3HBL2B43AL13AL33SPP3SPE3SLO3ACL3SPA4ACL0FS2PP4CRTV2SP2bs3AL13AL33SPA1r2HrFFS1L3HLS2lo2PP3END4CRTV2SP3BUF4BLEN2bs3HBL2B33AL13AL33SPP3SPE3SLO3ACL3SPA4ACL0". (* [comment removed for export] *)
  Lemma sum_crtextP_valid : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PQ,P,$5=.SpPLB0,(24.(1.$2.$2.))Plo,$2.PTOP,$2.PMO0,$2>.PAL,$23.PLAWS,(24.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PCS,P,$2.SpPOPSX,(24.Pm,P,(2<.&40.)(2=.(2<.&8.))Sp)PGX,(24.$2.)PPX,(24.Pvs,(24.$2.)Sp)PLX,(24.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)PR0,$5>.PR1,$5>.PHX,(24.$5>.)P,(8=.$26.VL,VHI,R10.)(60.$26.R;.(38.$2.(0.$2.R=.(0.$2.(32.VL,)(0.$2.(28.VL,)(0.$2.(33.VL,)(0.$2.(34.VL,)(0.$2.(35.VL,)(0.$2.R>.(5.$2.))))))))R7.)(0.Pm,P,(2<.&40.)(2=.(2<.&8.))Sp(43.$26.VL,)R8.)R:.(38.Pvs,(24.$2.)Sp(0.Pvs,(24.$2.)Sp(46.VL,R?.)(0.Pvs,(24.$2.)Sp(47.VL,R?.R>.R=.)(0.Pvs,(24.$2.)Sp(48.VL,R?.R>.)(0.Pvs,(24.$2.)Sp(61.R?.)(5.Pvs,(24.$2.)Sp)))))R6.)R?.(62.VL,VHI,R=.R<.)(63.VL,R=.)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(64.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(65.VL,)R5.))(0.$5>.R4.(0.$5>.R3.(0.$5>.(8>.VL,)R2.)))(68.$26.R10.)(8?.R11.)$81.R9.)")
(* [comment removed for export] *).
  Proof.
    intros pc Q LB0 lo TOP MO0 AL LAWS CS OPSX GX PX LX R0 R1 HX CRTEXT. cbn [app]. split; [reflexivity|]. unfold SUM_crtextP, HC_crtextP, havoc17, q. lx_sum_unfold.
    intros PP END CRTV NUL SP TPV TOP' HLS' ACE HLTP IMGLO IMGHI LO P BUF BLEN.
    intros bs.
    intros F fc m mo LB.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros _ _ MI G0 G1 G2 G3 G4 G5 G6 R10 R11 R12 R13 R2 R4 ST HPP HEXT [HBUF HBL].
    intros TP N0 B1 B2 B3 B4 NZB AL1 AL3 SPP PPT SPE EXT' D1 ACL SLO SPA HTOP SPB BK3.
    intros SOK EXT (h & HH & HT & MF) _ K1 _.
    unfold tgt_aevtM. intros MK. subst x10 x11 x12 x13 x2 x4. subst TOP' HLS' ACE HLTP IMGLO IMGHI LO TPV NUL.
    cbn [blkP] in BK3.
    pose proof (@alloc_ceiling_lo L) as ACL0.
    assert (HSP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply lx_uw64; unfold two64, X509_GET_CRT_EXT_STACK in *; lia).
    (* [comment removed for export] *)
    assert (HEXT' : rw_cells usegs m (CRTV + 424) [CB 272 (zeros 272)]).
    { eapply rw_cells_reshape; [exact HEXT| cbn; split; [reflexivity| exact I]| vm_compute; reflexivity]. }
    unfold x509_get_crt_ext_stmt in CRTEXT.
    eapply aevtM_cut.
    { eapply CRTEXT with (lo := lo) (bs := bs) (PP := PP) (CRT := CRTV) (P := P) (END := END) (BUF := BUF) (h := h) (LB := LB);
        rewrite ?HSP, ?HT, <- ?HBL; try reflexivity; try eassumption; try (unfold X509_GET_CRT_EXT_STACK, EXT_SIZE in *; lia).
      rewrite HBL. apply EXT; exact BK3. }
    clear CRTEXT. intros ms' mo2 PO. unfold x509_get_crt_ext_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & h' & r & p' & eo & ej & LBx & E & PO).
    injection E; intros <- ->. rewrite ?HSP in PO.
    destruct PO as (-> & Hr & MI' & SO' & ST' & MF' & HT' & HPP' & Hp' & HEXT2 & HOK & PERM & HH' & HPX).
    apply ext_cells_words in HEXT2. unfold ext_words in HEXT2. cbn [wchunks app] in HEXT2.
    lx_aevtM_zregs.
    destruct (heap_blocks _ _ HI _ _ _ _ HH') as [HBR HAP]. rewrite Forall_app in HBR. destruct HBR as [HBRx HBRl].
    eapply (K1 r _ _ _ _ _ _ _ _ _ _ _ _ _ _ p' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LBx ++ LB));
      try eassumption; try reflexivity; try exact I; try lia; try exact (heap_mok _ _ HI _ _ _ _ HH').
    - (* [comment removed for export] *)
      split; [| split; [apply RextP_ok; [exact DIM1| exact DIM2]| split; [apply cwP_blk| split; [constructor| split; [exact EXT| intros b Hb; apply in_or_app; right; exact Hb]]]]].
      exists eo, LBx. cbn [nth]. split; [reflexivity|]. split; [exact PERM|]. split; [| split; [exact HBRx| split; [exact HOK| repeat split; reflexivity]]].
      intros b Hb B k HBk. clear - HAP Hb HBk. induction LBx as [|[a n] LBx IH]; [destruct Hb|]. cbn [app blocks_apart] in HAP. destruct HAP as [HA HAP].
      destruct Hb as [<-|Hb]; [cbn [fst snd]; apply (HA B k); apply in_or_app; right; exact HBk| exact (IH HAP Hb)].
    - (* [comment removed for export] *)
      exists h'. split; [exact HH'| split; [rewrite HT'; exact HT| eapply mo_frame_trans; eassumption]].
    - (* [comment removed for export] *) intros b Hb. apply in_or_app. right. exact Hb.
    - (* [comment removed for export] *)
      unfold lawPX. change (CRTV + 424 + EXT_SIZE) with (CRTV + 424 + 272) in HPX.
      replace (CRTV + 424 + 272) with (CRTV + 696) in HPX by lia. exact HPX.
    all: match goal with |- ?G => idtac "LEFT"; idtac G end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma SUMS_extP_ok : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsCrt ()) "Ppc,$2.PQ,P,$5=.SpPLB0,(24.(1.$2.$2.))Plo,$2.PTOP,$2.PMO0,$2>.P,(8=.$26.VL,VHI,R6.)(51.$6:.(31.$26.$3>.(0.$2.R3.(0.$2.(32.VL,)(0.$2.(28.VL,)(0.$2.(33.VL,)(0.$2.(34.VL,)(0.$2.(35.VL,)(0.$2.R4.(5.$2.))))))))(0.Pm,P,(2<.&40.)(2=.(2<.&8.))Sp(43.$26.VL,)(0.P,P,(2<.&40.)(2=.(2<.&8.))Sp(3<.VL,VSI,)(5.P,P,(2<.&40.)(2=.(2<.&8.))Sp)))(5.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp)(0.Pvs,(24.$2.)Sp(46.VL,R5.)(0.Pvs,(24.$2.)Sp(47.VL,R5.R4.R3.)(0.Pvs,(24.$2.)Sp(48.VL,R5.R4.)(0.Pvs,(24.$2.)Sp(61.R5.)(5.Pvs,(24.$2.)Sp)))))R5.(62.VL,VHI,R3.R2.)(63.VL,R3.)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(64.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(65.VL,)(0.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp(66.VL,VSI,)(5.P,(24.(1.$2.$2.))P,$2.P,(24.(1.$2.$2.))P,P,(2<.&40.)(2=.(2<.&8.))P,P,(2<.&40.)(2=.(2<.&8.))Sp))))(0.$5>.(6;.VL,)(0.$5>.(67.VL,VPK,)(0.$5>.(8>.VL,)(5.$5>.))))(68.$26.R6.)L,$2.$3?.)(0.$6:.(8?.R7.)(5.$6:.)))")
(* [comment removed for export] *).
  Proof. intros. constructor; [| constructor]. eapply apply_summary_soundMR. apply (sum_crtextP_valid pc Q LB0 lo TOP MO0 _ [] _ [@si_P L SI] [] [] [lawPXS L SI] _ _ []). assumption. Qed.
End CrtExtValid.

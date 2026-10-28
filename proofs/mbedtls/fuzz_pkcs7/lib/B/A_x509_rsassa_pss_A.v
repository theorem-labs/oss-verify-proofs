(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int_loops A_asn1_get_int A_oid A_oid_md_alg A_asn1_get_alg A_asn1_get_alg_null A_x509_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_asn1_get_alg_A A_asn1_get_alg_null_A A_x509_hash_alg_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P05b773c0f5077e0e 1 2 64 2 0 1 74 1 64 2 56 1 75 1 2 76 1 77 1P0e4dac9304fd3ec6 0 2 0 1 85 1P124b9ec7e852eb68 0 2 0 1 85 1P13416d1a058dd299 0 2 0 1 85 1P17a8956ccaab2465 0 2 0 1 85 1P17dbfea3d6ea75b4 0 2 0 1 85 1P1c0e4b55389ac0a1 0 2 0 1 71 1P1f4b108c23c114cd 0 5 0 1 34 1 56 1 75 1 76 1P20bcf17175212844 0 5 0 1 36 1 85 1 88 1 89 1P22258accb825ad98 1 1 64 2 1 1 74 1 3 0 1 75 1 76 64P22ca927aff41e00c 0 2 0 1 85 1P244380fd7de0e023 0 2 0 1 85 1P263c54a9920d1866 0 4 0 32 35 32 88 32 89 32P2948b6ce308b848e 0 2 0 1 85 1P2eeed2eb66020946 1 1 64 2 56 1 75 1 3 0 1 74 1 76 64P3005527cf0c0d12e 0 2 0 1 85 1P31a739ebde716ba5 0 2 0 1 85 1P35b58fd6e0ce0d22 0 2 0 1 85 1P380ceca74ef45603 0 2 0 1 85 1P3b6efdba76139ba5 0 2 0 1 85 1P3d5a58e3d1de1652 0 2 0 1 85 1N03ecef711fd1030eN07bde7ef40e827f9N08f4040482a81c9cN09193ba557f1a368N0a7daef09567bbe0N0ac8f8e8675f643bN0bd29ab242119cceN0df49d27f737bb16N0f67483ec475d64fN0f87fefa432b74a7N10de3080a172d867N11a97d25e79dd827N1330b7e21a280773N17f14f4aa7869d4eN1e95567111640219N206fffc64751e500N21681e80e1223072N24f1abbca1d78412N264db5fec8139678N2c4ac39e4770a73cN2f993b8fe342a833N345478f86385cc29N36680955b55eb700N3a6bc5c68e237d07N3bcf994b004d13bdN3ca9c56a98313ff1N3d7ad055c3389026"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_x509_rsassa_pss_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "X509_PSS_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "x509_pss_postA"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "pss_fshl"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wlow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.shadow_free"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "stdpp.bitvector.definitions.bv_swrap"; "pss_fctx"].


Definition A_X509_RSASSA_PSS : Z := 0x0ac148.      (* [comment removed for export] *)
Definition A_SMALLOC_2P : Z := 0x531fc.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PSS_MGF1_OID : Z := 0x26540.          (* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
Definition X509_PSS_STACK_A : Z := 4384.

Definition x509_pss_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (MD MGF SALT lo slo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.O1>.O1=.O1<.)Lh',(4.O1>.O1=.O1<.)(1.$5.Lr,$5.(1.(2.&40.)Lv1,(2.&40.)(1.(2.&40.)Lv2,(2.&40.)(1.(2.&40.)Lv3,(2.&40.)(6.(7.$0.R16.(8.(9.O18.O17.O16.O15.R15.R14.R13.O14.O13.R12.R11.R10.R?.R>.R=.R<.R;.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R:.R9.R8.R7.)O8.(:.O18.)O7.(;.(2.&40.))R6.(<.O1>.)))(6.(=.O1>.O1=.O1<.R5.O1:.O19.R6.)(6.(7.P,$5.Sp(>.O1>.O1=.O1<.R5.)(>.O1>.O1=.O1<.O1;.))(6.(7.$5.(?.O1>.O1=.O1<.R5.)(?.O1>.O1=.O1<.O1;.))(6.(7.$5.(10.O1>.O1=.O1<.R5.)(10.O1>.O1=.O1<.O1;.))(6.(7.$5.(11.O1>.O1=.O1<.R5.)(11.O1>.O1=.O1<.O1;.))(6.(7.$5.(12.O1>.O1=.O1<.R5.)(12.O1>.O1=.O1<.O1;.))(6.(7.$5.(13.O1>.O1=.O1<.R5.)(13.O1>.O1=.O1<.O1;.))(6.Pmo,$14.(15.(16.O1>.O1=.O1<.R6.R1.)(16.O1>.O1=.O1<.O1;.R1.))(6.(17.O1>.O1=.O1:.O19.(18.&40.O17.)(18.&40.O17.)(10.O1>.O1=.O1<.O1;.)(19.(1:.$5.$5.)(1;.$5.$5.O6.(1<.O6.+4.))(19.(1:.$5.$5.)(1;.$5.$5.O5.(1<.O5.+4.))(19.(1:.$5.$5.)(1;.$5.$5.O4.(1<.O4.+4.))(1=.(1:.$5.$5.)))))O1.R6.)(6.(1>.O1>.R6.)(6.(1?.O1>.R6.O3.(18.&40.O17.))(6.(20.O1>.(21.O1=.)R6.O2.(18.&40.O17.))(6.(7.(2.&40.)R12.(22.&40.R4.))(6.(6.(23.-3000.R4.)(24.R4.=))(6.(25.O1>.R6.O6.(19.$26.(27.R3.)(1=.$26.)))(6.(25.O1>.R6.O5.(19.$26.(27.R2.)(1=.$26.)))(25.O1>.R6.O4.(19.$26.(27.R1.)(1=.$26.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_pss_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "Ph,(4.O4.O3.O2.)PLB,(28.$29.)PLF,(28.$29.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPAR,$5.PMD,$5.PMGF,$5.PSALT,$5.PBUF,$5.Ppp,$5.Plo,$5.Pslo,$5.Pbs,(28.(2.&8.))Pptag,(2.&40.)Pppad,(2.&40.)Pplen,(2.&40.)Pv1,(2.&40.)Pv2,(2.&40.)Pv3,(2.&40.)P,(=.O4.O3.O2.R34.R33.R32.R10.)P,(2;.(2<.$29.R33.)#1??.)P,(25.O4.R12.R11.(19.$26.(27.R8.)(19.$26.(27.R7.)(19.$26.(2=.R6.)(19.$26.(2=.(22.&40.R<.))(1=.$26.))))))P,(25.O4.R13.R11.(19.$26.(27.R6.)(1=.$26.)))P,(25.O4.R14.R11.(19.$26.(27.R6.)(1=.$26.)))P,(25.O4.R15.R11.(19.$26.(27.R6.)(1=.$26.)))P,(2>.O4.R16.R11.R=.)P,(2?.(6.(7.$5.R11.=)(7.$5.(18.&40.R;.)=))(6.(24.R12.R11.)(24.(1<.R11.(18.&40.R;.))(1<.R12.(30.(2<.(2.&8.)R>.))))))P,(24.(1<.(1<.R13.(30.(2<.(2.&8.)R?.)))+8.)(31.+2.+2?.))P,(2?.(24.(1<.R17.+4.)R16.)(24.(1<.R16.+4.)R17.))P,(2?.(24.(1<.R18.+4.)R16.)(24.(1<.R16.+4.)R18.))P,(2?.(24.(1<.R18.+4.)R17.)(24.(1<.R17.+4.)R18.))P,(2?.(24.(1<.R1:.+4.)R1;.)(24.(1<.R1;.+18.)R1:.))P,(2?.(24.(1<.R1:.+4.)R1<.)(24.(1<.R1<.+18.)R1:.))P,(2?.(24.(1<.R1:.+4.)R1=.)(24.(1<.R1=.+18.)R1:.))P,(2?.(7.$5.(30.(2<.(2.&8.)R16.))=)(2?.(24.(1<.R1=.+4.)R1:.)(24.(1<.R1:.(30.(2<.(2.&8.)R16.)))R1=.)))P,(2?.(7.$5.(30.(2<.(2.&8.)R17.))=)(2?.(24.(1<.R1=.+4.)R1;.)(24.(1<.R1;.(30.(2<.(2.&8.)R17.)))R1=.)))P,(2?.(7.$5.(30.(2<.(2.&8.)R18.))=)(2?.(24.(1<.R1=.+4.)R1<.)(24.(1<.R1<.(30.(2<.(2.&8.)R18.)))R1=.)))P,(7.$5.(32.R21.+8.)=)P,(7.$5.(32.R21.+4.)=)P,(7.$5.(32.R21.+4.)=)P,(7.$5.(32.R21.+4.)=)P,(6.(23.=R25.)(24.(1<.R25.+18.)(31.+2.+40.)))P,(6.(23.=R25.)(24.(1<.R25.+4.)(31.+2.+40.)))P,(6.(23.=R25.)(24.(1<.R25.+4.)(31.+2.+40.)))P,(6.(23.=R25.)(24.(1<.R25.+4.)(31.+2.+40.)))P,(23.=R25.)P,(1?.O4.R2;.R24.(18.&40.R4;.))P,(20.O4.(21.O3.)R2<.R24.(18.&40.R4<.))P,(24.R26.(33.(18.&40.R4=.)$34.))P,(24.R27.(33.(33.(18.&40.R4>.)+120.)(35.O3.)))P,(24.=(35.O3.))P,(24.R29.(33.(33.(18.&40.R50.)+1>0.)(36.O3.)))P,(24.=(36.O3.))P,(24.R2;.(33.(33.(18.&40.R52.)+160.)(37.O3.)))P,(24.=(37.O3.))P,(24.(38.O3.)R2<.)P,(24.R2=.R2>.)P,(7.$5.(32.(18.&40.R56.)+10.)=)P,(24.(18.&40.R57.)(?.O4.O3.O2.R5;.))P,(24.(18.&40.R58.)(31.+2.+2?.))P,(2?.(24.(1<.R38.+18.)R32.)(24.(18.&40.R59.)R38.))P,(2?.(24.(1<.R38.+4.)R33.)(24.(18.&40.R5:.)R38.))P,(2?.(24.(1<.R38.+4.)R34.)(24.(18.&40.R5;.)R38.))P,(2?.(24.(1<.R38.+4.)R35.)(24.(18.&40.R5<.)R38.))P,(2?.(7.$5.(30.(2<.(2.&8.)R34.))=)(2?.(24.(1<.R38.(30.(2<.(2.&8.)R34.)))R36.)(24.(18.&40.R5=.)R38.)))P,(39.(3:.O3.)(3;.$29.R61.(3<.R60.))R37.R3=.+18.)P,(39.(3:.O3.)(3;.$29.R62.(3<.R61.))R38.R3=.+4.)P,(39.(3:.O3.)(3;.$29.R63.(3<.R62.))R39.R3=.+4.)P,(39.(3:.O3.)(3;.$29.R64.(3<.R63.))R3:.R3=.+4.)P,(39.(3:.O3.)(3;.$29.R65.(3<.R64.))R3;.R3=.(30.(2<.(2.&8.)R39.)))P,(3=.(3:.O3.)(3;.$29.R66.(3<.R65.))R3<.(?.O4.O3.O2.R67.)R41.+4.)P,(3=.(3:.O3.)(3;.$29.R67.(3<.R66.))R3=.(?.O4.O3.O2.R68.)R41.+4.)P,(3=.(3:.O3.)(3;.$29.R68.(3<.R67.))R3>.(?.O4.O3.O2.R69.)R41.+4.)P,(1>.O4.R46.)P,(7.(2.&40.)R65.(22.&40.(3>.O3.)))P,(3?.O4.(21.O3.)(>.O4.O3.O2.R6<.)R48.R47.+18.)P,(3?.O4.(21.O3.)(>.O4.O3.O2.R6=.)R49.R47.+4.)P,(3?.O4.(21.O3.)(>.O4.O3.O2.R6>.)R4:.R47.+4.)P,(3?.O4.(21.O3.)(>.O4.O3.O2.R6?.)R4;.R47.+4.)P,(3?.O4.(21.O3.)(>.O4.O3.O2.R70.)R4<.R47.(30.(2<.(2.&8.)R43.)))P,(7.(2.&40.)R65.(22.&40.R4<.))P,(7.(2.&40.)R65.(22.&40.R4<.))P,(7.(2.&40.)R65.(22.&40.R4<.))P,(7.(2.&40.)R65.(22.&40.R4<.))(40.O4.(21.O3.)(>.O4.O3.O2.R75.)(41.O4.O3.O2.R75.R74.R73.R72.R71.R70.R6?.R6;.R6:.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R53.R52.R4?.R4>.R4=.R4:.R49.R51.)(8.(9.R72.R71.R70.R6?.R6>.R6=.R6<.R6;.R6:.R69.R68.R67.R66.R65.R64.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.)R53.(22.&40.O1.)R52.(;.(2.&40.))R51.(<.O4.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition pss_fshl : list cell := ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "(19.$26.(42.(22.&8.+?1.))(19.$26.(42.(22.&8.+?1.))(19.$26.(42.(22.&8.+?1.))(19.$26.(42.(22.&8.+?1.))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.=))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?2.))(19.$26.(42.(22.&8.+?8.))(19.$26.(42.(22.&8.+?3.))(19.$26.(42.(22.&8.+?3.))(19.$26.(42.(22.&8.+?3.))(1=.$26.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition pss_fctx (R : art_layout) (HIA : artA asegs R) (h : HST asegs R HIA) (LB LF : list blk)
    (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (PAR MD MGF SALT BUF lo slo : Z) (bs : list byte)
    (FB sp1 : Z) (h1 : HST asegs R HIA) (m0 mm : mem) (w0 w1 w2 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "(6.(=.$43.O23.O22.O6.O20.(19.(1:.$5.$5.)(1;.$5.$5.O8.+100.)O1?.)O4.)(6.(7.P,$5.Sp(>.$43.O23.O22.O6.)(>.$43.O23.O22.O21.))(6.(7.$5.(?.$43.O23.O22.O6.)(?.$43.O23.O22.O21.))(6.(7.$5.(10.$43.O23.O22.O6.)(10.$43.O23.O22.O21.))(6.Pmo,$14.(15.(16.$43.O23.O22.O6.R1.)(16.$43.O23.O22.O21.R1.))(6.(7.$5.(11.$43.O23.O22.O6.)(11.$43.O23.O22.O21.))(6.(7.$5.(12.$43.O23.O22.O6.)(12.$43.O23.O22.O21.))(6.(7.$5.(13.$43.O23.O22.O6.)(13.$43.O23.O22.O21.))(6.(6.(24.(33.(18.&40.O1=.)+;0.)O7.)(24.O7.(33.(18.&40.O1=.)+:0.)))(6.(7.$5.(32.O7.+20.)=)(6.(25.$43.O4.O8.(19.$26.(2=.O3.)(19.$26.(2=.O2.)(19.$26.(2=.O1.)(1=.$26.)))))(6.(25.$43.O4.(1<.(44.O8.+3.)(45.(21.O23.)))$46.)(6.(47.(>.$43.O23.O22.O21.)O8.+100.)(6.(7.$5.(32.O8.+20.)=)(6.(23.=O8.)(6.(24.(1<.O8.+100.)O7.)(6.(3=.(3:.O23.)(3;.$29.O20.(3<.(19.(1:.$5.$5.)(1;.$5.$5.O8.+100.)O1?.)))(38.O23.)(?.$43.O23.O22.O21.)O8.+18.)(6.(3=.(3:.O23.)(3;.$29.O20.(3<.(19.(1:.$5.$5.)(1;.$5.$5.O8.+100.)O1?.)))(38.O23.)(?.$43.O23.O22.O21.)(1<.O8.+20.)+=8.)(6.Px,$5.P,(6.(24.O8.R1.)(23.R1.(1<.O8.+100.)))(2?.(6.(24.(38.O23.)R2.)(23.R2.(?.$43.O23.O22.O21.)))(48.(19.(1:.$5.$5.)(1;.$5.$5.O8.+100.)O1?.)R2.))(6.Pb,$29.P,(49.$29.R1.(3;.$29.O20.(3<.O1?.)))(49.$29.R2.(3;.$29.O20.(3<.(19.(1:.$5.$5.)(1;.$5.$5.O8.+100.)O1?.))))(6.(2?.(24.(1<.O8.+100.)O10.)(24.(1<.O10.+18.)O8.))(6.(2?.(24.(1<.O8.+100.)O?.)(24.(1<.O?.+4.)O8.))(6.(2?.(24.(1<.O8.+100.)O>.)(24.(1<.O>.+4.)O8.))(6.(2?.(24.(1<.O8.+100.)O=.)(24.(1<.O=.+4.)O8.))(6.(2?.(7.$5.(30.(2<.(2.&8.)O9.))=)(2?.(24.(1<.O8.+100.)O<.)(24.(1<.O<.(30.(2<.(2.&8.)O9.)))O8.)))(6.(1?.$43.O4.O;.O7.)(6.(24.(1<.O8.+100.)(38.O23.))(6.(1?.$43.O4.O7.(1<.(18.&40.O1=.)-68.))(6.(25.$43.O4.(1<.(18.&40.O1=.)-68.)(19.$26.(2=.O11.)(19.$26.(2=.O12.)(19.$26.(2=.O13.)(19.$26.(2=.O14.)(19.$26.(2=.O15.)(19.$26.(2=.O16.)(19.$26.(2=.O17.)(19.$26.(2=.O18.)(19.$26.(2=.O19.)(19.$26.(2=.O1:.)(19.$26.(2=.O1;.)(19.$26.(2=.O1<.)(19.$26.(2=.O1>.)(1=.$26.)))))))))))))))(6.(3?.$43.(21.O23.)(>.$43.O23.O22.O21.)O4.O?.+4.)(6.(3?.$43.(21.O23.)(>.$43.O23.O22.O21.)O4.O>.+4.)(6.(3?.$43.(21.O23.)(>.$43.O23.O22.O21.)O4.O=.+4.)(6.(1>.$43.O4.)(6.(4:.$43.O23.O22.O21.O20.O1?.(18.&40.O1=.)(18.&40.O1=.)(19.(1:.$5.$5.)(1;.$5.$5.O?.(1<.O?.+4.))(19.(1:.$5.$5.)(1;.$5.$5.O>.(1<.O>.+4.))(19.(1:.$5.$5.)(1;.$5.$5.O=.(1<.O=.+4.))(1=.(1:.$5.$5.)))))O5.O4.)(6.(4;.O23.O20.O1?.)(6.(4<.O23.O20.O1?.(18.&40.O1=.)(19.(1:.$5.$5.)(1;.$5.$5.O?.(1<.O?.+4.))(19.(1:.$5.$5.)(1;.$5.$5.O>.(1<.O>.+4.))(19.(1:.$5.$5.)(1;.$5.$5.O=.(1<.O=.+4.))(1=.(1:.$5.$5.)))))O8.+100.)(6.(4=.O23.O20.O1?.(18.&40.O1=.)(10.$43.O23.O22.O21.)O8.+100.)(6.(20.$43.(21.O23.)O4.O:.O7.)(6.(20.$43.(21.O23.)O4.O7.(18.&40.O1=.))(6.(4>.O23.O20.O1?.O8.+100.)(7.$5.(32.O8.+40.)=)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11158032613.12L25876784085.20L29784460045.12L35939077855.12L45146172909.1200000;00]00c00m01=S1B1k2H02HkS1B1k2r02HB2Hk1a2Ha1q1r1H2H02q02H4S1B2H0S3ALx1B2H0S1B1k2H02Hk1a2Ha". (* [comment removed for export] *)
Lemma aobj_partial : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "PALx,$4?.PCSx,P,$5.SpPmX,P,(2.&40.)(3.(2.&8.))PB,$5.Pk,$5.P,(25.$43.R3.(1<.(44.R2.+3.)(45.R5.))(19.$26.(42.(22.&8.R1.))(1=.$26.)))P,(7.$5.(32.R3.+8.)=)P,(24.=R4.)P,(6.(24.+1.R4.)(24.R4.+7.))P,(47.R8.R6.R5.)(3?.$43.R:.R9.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros ALx CSx mX B k H HB H0 Hk HC. split; [exact HC|]. intros a Ha. exists (Z_to_bv 8 k). split.
  - rewrite (shadow_of_granule ALx a B HB ltac:(lia)).
    replace (shadow_of ALx B) with (Z.shiftr B 3 + al_sb ALx) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    destruct H as [[_ HB'] _]. cbn [cells_bytes cbytes app] in HB'. exact HB'.
  - right. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
    clear - Ha HB Hk. Z.div_mod_to_equations. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0xac620]).
Local Ltac zchk_new ::= constr:([0xac1fc; 0xac204; 0xac21c; 0xac248; 0xac260; 0xac264; 0xac268; 0xac270; 0xac290; 0xac2ac; 0xac2b0; 0xac2bc; 0xac2c0; 0xac2c4; 0xac2c8; 0xac2e0; 0xac2e4; 0xac2e8; 0xac2ec; 0xac2fc; 0xac304; 0xac308; 0xac30c; 0xac328; 0xac32c; 0xac334; 0xac338; 0xac33c; 0xac340; 0xac388; 0xac38c; 0xac390; 0xac394; 0xac398; 0xac39c; 0xac3dc; 0xac3e0; 0xac3e4; 0xac3e8; 0xac3ec; 0xac400; 0xac404; 0xac408; 0xac40c; 0xac414; 0xac428; 0xac42c; 0xac434; 0xac438; 0xac47c; 0xac480; 0xac484; 0xac488; 0xac48c; 0xac490; 0xac494; 0xac4b0; 0xac4b8; 0xac4c4; 0xac4d0; 0xac4d8; 0xac4f0; 0xac4f4; 0xac4fc; 0xac500; 0xac504; 0xac534; 0xac548; 0xac558; 0xac55c; 0xac560; 0xac564; 0xac568; 0xac59c; 0xac5c0; 0xac5c4; 0xac5c8; 0xac5cc; 0xac5d0; 0xac5d4; 0xac5d8; 0xac5fc; 0xac604; 0xac614; 0xac61c]).
Local Ltac zchk_unpin ::= lx_unpin.
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GSBH : al_gsb AL = AGSB.
  Hypothesis MCI : arl_memcmp_i R = A_WRAP_BCMP.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis GI : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG 64.
  Hypothesis GALG : asn1_get_alg_stmtA asegs R HIA A_ASN1_GET_ALG.
  Hypothesis GNULL : asn1_get_alg_null_stmtA asegs R HIA A_ASN1_GET_ALG_NULL.
  Hypothesis GHASH : x509_hash_stmtA asegs R HIA A_X509_HASH_ALG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo slo : Z) (bs : list byte) (ptag ppad plen : word).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis HAP : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "(2?.(6.(7.$5.Vpp,=)(7.$5.(18.&40.Vplen,)=))(6.(24.VBUF,Vpp,)(24.(1<.Vpp,(18.&40.Vplen,))(1<.VBUF,(30.(2<.(2.&8.)Vbs,))))))")
(* [comment removed for export] *).
  Hypothesis B47 : BUF + Z.of_nat (length bs) + 8 <= 2^47.
  Hypothesis D12 : MD + 4 <= MGF \/ MGF + 4 <= MD.
  Hypothesis D13 : MD + 4 <= SALT \/ SALT + 4 <= MD.
  Hypothesis D23 : MGF + 4 <= SALT \/ SALT + 4 <= MGF.
  Hypothesis D1P : MD + 4 <= PAR \/ PAR + 24 <= MD.
  Hypothesis D2P : MGF + 4 <= PAR \/ PAR + 24 <= MGF.
  Hypothesis D3P : SALT + 4 <= PAR \/ PAR + 24 <= SALT.
  Hypothesis D1B : Z.of_nat (length bs) = 0 \/ MD + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MD.
  Hypothesis D2B : Z.of_nat (length bs) = 0 \/ MGF + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MGF.
  Hypothesis D3B : Z.of_nat (length bs) = 0 \/ SALT + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= SALT.
  Hypothesis ALP : PAR mod 8 = 0.
  Hypothesis AL1 : MD mod 4 = 0.
  Hypothesis AL2 : MGF mod 4 = 0.
  Hypothesis AL3 : SALT mod 4 = 0.
  Hypothesis PARB : 0 < PAR /\ PAR + 24 <= 2^64.
  Hypothesis MDB : 0 < MD /\ MD + 4 <= 2^64.
  Hypothesis MGFB : 0 < MGF /\ MGF + 4 <= 2^64.
  Hypothesis SALTB : 0 < SALT /\ SALT + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_PSS_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 288 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLO4 : lo <= bv_unsigned sp - 480 - arl_need_amem R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis SLO5 : lo <= bv_unsigned sp - 352 - arl_need_bcmp R.
  Hypothesis RTB0 : 0 <= arl_need_bcmp R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DSP : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS1 : MD + 4 <= lo \/ bv_unsigned sp <= MD.
  Hypothesis DS2 : MGF + 4 <= lo \/ bv_unsigned sp <= MGF.
  Hypothesis DS3 : SALT + 4 <= lo \/ bv_unsigned sp <= SALT.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CRP : client_range L (LB ++ fdata LF) lo PAR 24.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo MD 4.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo MGF 4.
  Hypothesis CR3 : client_range L (LB ++ fdata LF) lo SALT 4.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MD 4.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MGF 4.
  Hypothesis CW3 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SALT 4.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_PSS_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_pss_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo slo).
  Local Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation fctx := (pss_fctx R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 PAR MD MGF SALT BUF lo slo bs).

  Ltac fctx_open D :=
    destruct D as (HH & ECS & ETOP & ESTK & HKI & EFLAG & EVOL & EFR & SP1 & SP1M & FH & FSH & CFB & FBAL & FB0 & FBS1
                   & FWH & FWD & FWS & SUBLF & APP & AP1 & AP2 & AP3 & AP4 & ST1 & SEPF & STK2 & SPILL & OMD & OMGF & OSALT & MI & PRES & WL & WCF & SFF
                   & SS1 & SS2 & FRSH & F64);
    unfold pss_fshl in FSH.
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  (* [comment removed for export] *)
  Ltac fctx_build :=
    lazymatch goal with |- pss_fctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac end;
    unfold pss_fctx, pss_fshl; spine; first [ eassumption | match goal with |- ?g => idtac "FCTX-LEFT:" g end ].

  (* [comment removed for export] *)
  Lemma swrap32_errsum' : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "Pr,$5.Pc,$5.P,(6.(23.-10000.R2.)(24.R2.=))P,(6.(24.(33.(31.+2.+40.)+10000.)R2.)(23.R2.(31.+2.+40.)))(7.$5.(50.&20.(1<.(32.R4.+10000000000000000.)R3.))(1<.R4.(33.R3.(31.+2.+40.))))")
(* [comment removed for export] *).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  Ltac fin_postA PRES :=
    apply evtA_done; unfold x509_pss_postA;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    [ lazymatch goal with |- HM _ _ _ _ _ _ _ => eassumption end | ..];
    (lazymatch goal with
     | |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ => exact H end
     | _ => idtac end);
    (lazymatch goal with
     | |- presA _ _ _ _ _ _ _ _ _ _ => eapply presW_presA; exact PRES
     | |- rw_cells _ _ _ _ => idtac
     | |- forall mo, HK _ _ _ _ mo <-> _ =>
         first [ assumption
               | let mo' := fresh "mo" in intros mo';
                 repeat (eapply iff_trans; [ match goal with H : forall mo, HK _ _ _ _ mo <-> _ |- _ => apply H end | ]);
                 apply iff_refl ]
     | |- _ => first [ assumption | reflexivity | congruence | (clear_disj; clear_mods; lia) | idtac ] end).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 CW3; try lx_pin1 CW2; try lx_pin1 CW1; try lx_pin1 CR4; try lx_pin1 CRP; try lx_pin1 DS4; try lx_pin1 DS3; try lx_pin1 DS2; try lx_pin1 DS1; try lx_pin1 DSP; try lx_pin1 SPA; try lx_pin1 RTB0; try lx_pin1 SLO5; try lx_pin1 RTA0; try lx_pin1 SLO4; try lx_pin1 RTS0; try lx_pin1 SLO3; try lx_pin1 BUF0; try lx_pin1 AL3; try lx_pin1 AL2; try lx_pin1 AL1; try lx_pin1 ALP; try lx_pin1 D3B; try lx_pin1 D2B; try lx_pin1 D1B; try lx_pin1 D3P; try lx_pin1 D2P; try lx_pin1 D1P; try lx_pin1 D23; try lx_pin1 D13; try lx_pin1 D12; try lx_pin1 B47; try lx_pin1 HAP; try lx_pin1 plen; try lx_pin1 ppad; try lx_pin1 ptag; try lx_pin1 bs; try lx_pin1k slo; try lx_pin1k lo; try lx_pin1 pp; try lx_pin1 BUF; try lx_pin1 PAR; try lx_pin1k m; try lx_pin1 t6; try lx_pin1 t5; try lx_pin1 t4; try lx_pin1 t3; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 t2; try lx_pin1 t1; try lx_pin1 t0; try lx_pin1 ra; try lx_pin1k LF; try lx_pin1k LB; try lx_pin1k h; try lx_pin1 GHASH; try lx_pin1 GNULL; try lx_pin1 GALG; try lx_pin1 MDALG; try lx_pin1 GI; try lx_pin1 GT; try lx_pin1 MCI; try lx_pin1 GSBH.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01G0@D10598676144.139D2459793318.139 D32452690557.139D32604263319.140D3385894025.138 D45702188344.138D53304480533.139D57164004202.139D62011770188.140D62022258533.139D62022716265.138D6897102031.138 L1685717371.0   L19546883924.123L19594701403.2  L24876536089.172L30443668812.8  L30469992692.177L33213342763.2  L35488231161.130L39268637205.0  L39844638933.0  L40379729337.189L41486840212.2  L42411609006.0  L48117620905.121L48911768491.1  L5070094961.123 L50790731766.8  L51878069071.2  L52511154273.3  L54488093861.190L54860817083.2  L57570196295.2  L61490559858.177L61738609333.128L61745577556.5  L62018535662.1  L65276887194.120L66232301891.3  L6912107245.120 L9873114841.7   P41479713552.182P57577290179.183Q10523111609.145Q10592386204.144Q16178749881.144Q23925414036.152Q23927511184.145Q25144513881.181Q26030354684.181Q26032252605.155Q30280497419.149Q34964698202.181Q34966725147.155Q35653441506.190Q35660991248.149Q37578510242.148Q38250992823.153Q39035041096.181Q4110986150.180 Q42439443119.181Q42441479407.157Q4279611329.181 Q43076993659.148Q43878048875.153Q4467592451.150 Q47230721788.145Q49293189221.145Q5935758158.181 Q59865321072.181Q59867617328.157Q60109315147.190Q62009673036.152Q62011770184.145Q64133651577.181Q65266402725.143Q65276887190.151Q65276887194.146Q66222295478.145Q66345248714.150Q6897428434.143 Q6912107233.151 Q6912107245.146 Q7917062810.145 Q8699115497.181 Q8701272489.157 00000?00@00O00g00h01701801G01X01i02:02I02J03C03D03X03i04604704V04W04X04j04k04l05H05L06E06V06W06X07107207307@07W07j07m08808908D08`08a08b08o09:09E09U0:10:A0:X0:j0;60;U0;o0<Q0<]0<h0=30=C0=P0=h0>;0>H0>S0>a0>n0?<0?=0?J0?K0?L0?`0?j0@40@A0@L0@W0@b0@c0A00A;0AF0AQ0Ac0BP0C8S2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S1R3HIA2LF3LFB2FB3sp12h1FS2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1S2LF3LFB2FB3sp1SS1R2LF2sp2lo3LFB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACVFS2LF3LFB2FB3sp11p2PBS1R2sp2lo3SLO3LOSS2LF3LFB1r2RRFS1R2LF3slo3LFB4SLOS2FB3sp14SEPFSSS2LF2sp3LFB2FB3sp1FSS1R2LF2sp2lo3LFB3SLO3LOS3ALOS2FBS1R2LF2sp2lo3LFB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACVS1R2sp2lo3SLO3LOSFFS2LF2sp2lo3LFB3SLO2FB3sp1FFS2LF3LFB1r2RRS2LF2sp3LFB2FB3sp14FBS1S2sp2lo3SLO3sp13SP1S1RS2LF3LFB2FBFS2LF3LFB2FBS2sp2lo3slo3SLO4SLOL3sp13SP1FFS1R2LF2sp3LFBS2LF3LFB2FBS2LF3LFB2FBS1R3HIA1h2LF3LFBS1R3HIA1h2LF2sp3LFB3TOP4HTOPS2LF3LFB2FB1p2PBS2LF2sp2lo3LFB3sp11p2PBS2LF2sp2lo3LFB3sp1S2LF3MGF3LFBS2LF2sp2lo3LFB3SLO3sp13SP11p2PBS2LF2sp2lo3LFB3SLO3sp13SP1S1R3HIA1h2LF2sp2lo2bs3LFB3TOP4HTOPS2LF3MGF3LFBS2LF2MD3LFBS2LF2lo3LFBS2LF3LFB2FB1p2PBS2LF3LFB1p2PBS1R2LF3slo3LFB4SLOS1p2PBS1R2LF3slo3LFB4SLOSS2LF3LFB1p2PBS2LF2MD3LFBS2LF2sp2lo3LFBS2LF4SALT3LFBS1R2LF3LFB3ALOFS2LF3LFB1p2PBFFS1R2LF2lo2bs3LFB3LOSS1R2LF3LFBS1R2LF3LFBS2LF3LFB1p2PBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS2LF4SALT3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB4SEPFS1R3HIA1h2LF2sp3slo3LFB3TOP3sp13SP14HTOP1p2PBS1R3HIA1h2LF2sp3slo3LFB3TOP3sp13SP14HTOP". (* [comment removed for export] *)
  #[using="CR3 CR2 CR1 SPH TOP LOS SLOL SLOS SLO SALTB MGFB MDB PARB LFB IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "PFB,$5.Psp1,$5.Ph1,(4.$43.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps9v,(2.&40.)Ps10v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pr,$5.Pv1,(2.&40.)Pv2,(2.&40.)Pv3,(2.&40.)P,(51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VPAR,VMD,VMGF,VSALT,VBUF,Vlo,Vslo,Vbs,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)P,(25.$43.R1?.VMD,(19.$26.(27.R4.)(1=.$26.)))P,(25.$43.R20.VMGF,(19.$26.(27.R4.)(1=.$26.)))P,(25.$43.R21.VSALT,(19.$26.(27.R4.)(1=.$26.)))P,(6.(23.-3000.R8.)(24.R8.=))(40.$43.(21.VR,)(>.$43.VR,VHIA,Vh,)(41.$43.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,R24.)(8.(9.R1?.(22.&40.R26.)Vgp,Vtp,R1>.R1=.R1<.Vsp,(22.&40.R26.)(22.&40.R9.)R1;.R1:.R19.R18.R17.R16.R15.(22.&40.R27.)R14.R13.R12.R11.R10.(22.&40.R27.)R?.R>.(22.&40.(1<.(44.R27.+3.)(45.(21.VR,))))R=.R<.R;.R:.)VF,(22.&40.+:<628.)Vfc,(;.(2.&40.))R23.(<.$43.)))")
(* [comment removed for export] *).
  Proof.
  intros until v3.
  intros D HMD HMGF HSALT RR.
  fctx_open D.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xac6e0] [] 439%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH5 end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  match goal with H : HM _ _ _ h1 LB _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h1 LB ((FB, 256) :: LF) me FB 256 HHe ltac:(left; reflexivity))
  as (p & h2 & ROp & [old Hold] & CRp & NCp & NSp & HM2 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKiff2).
  replace (FB + 256 - 8) with (FB + 248) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB' : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, 256) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  pose proof (nc_apart _ _ _ _ _ p MD 4 NCp CR1 SUB' LOS ltac:(clear; lia)) as NP1.
  pose proof (nc_apart _ _ _ _ _ p MGF 4 NCp CR2 SUB' LOS ltac:(clear; lia)) as NP2.
  pose proof (nc_apart _ _ _ _ _ p SALT 4 NCp CR3 SUB' LOS ltac:(clear; lia)) as NP3.
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp : wcover R LB LF (bv_unsigned sp) W p 1)
  by (eapply wcover_nc; [exact NCp| exact SUB'| first [ clear - LOS SLO; lia | lx_side_lia ]]).
  rewrite ECS in CRp.
  clear HHe NCp NSp.
  (* [comment removed for export] *)
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM2.
  rewrite Z.eqb_refl in HM2.
  try (match goal with H : stk _ mf sp1 (bv_unsigned sp + -104) |- _ =>
        pose proof (stk_merge asegs mf lo sp1 _ ST1 H ltac:(first [ clear - SP1 SLO; lia | lx_side_lia ])) as ST3; clear ST1 H end).
  try (match goal with H : rw_cells _ mf (bv_unsigned sp + -104) _ |- _ => release_frame H ST3 (bv_unsigned sp) end).
  assert (SSF : sshad asegs AL mf slo (bv_unsigned sp)) by (eapply sshad_merge; [exact SS1| exact SS2| first [ clear - SP1 SLOL SLO; lia | lx_side_lia ]]).
  lxr_stk_join. fin_postA PRES.
  all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L29010717440.124L43090215975.2  L55542273011.2  L60010572849.2  00000100700=00>FS1r2RRS1r2RRS". (* [comment removed for export] *)
  Lemma err_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "PFB,$5.Psp1,$5.Ph1,(4.$43.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps9v,(2.&40.)Ps10v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pr,$5.Pv1,(2.&40.)Pv2,(2.&40.)Pv3,(2.&40.)P,(51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VPAR,VMD,VMGF,VSALT,VBUF,Vlo,Vslo,Vbs,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)P,(25.$43.R1?.VMD,(19.$26.(27.R4.)(1=.$26.)))P,(25.$43.R20.VMGF,(19.$26.(27.R4.)(1=.$26.)))P,(25.$43.R21.VSALT,(19.$26.(27.R4.)(1=.$26.)))P,(6.(23.-100.R8.)(24.R8.=))(40.$43.(21.VR,)(>.$43.VR,VHIA,Vh,)(41.$43.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,R24.)(8.(9.R1?.(22.&40.R26.)Vgp,Vtp,R1>.R1=.R1<.Vsp,(22.&40.R26.)(22.&40.R9.)R1;.R1:.R19.R18.R17.R16.R15.(22.&40.R27.)R14.R13.R12.R11.R10.(22.&40.R27.)R?.R>.(22.&40.(1<.(44.R27.+3.)(45.(21.VR,))))R=.R<.R;.R:.)VF,(22.&40.+:<60<.)Vfc,(;.(2.&40.))R23.(<.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until v3. intros D HMD HMGF HSALT RR.
    (* [comment removed for export] *)
    zstep. zstep. zpre; step; zsimp.
    first [ rewrite swrap32_errsum' by (clear - RR; lia) | match goal with |- ?g => idtac "ERR-FORM:" g end ].
    zpre.
    eapply epi_walk; first [ eassumption | clear - RR; lia | match goal with |- ?g => idtac "ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L3574711452.0000001S". (* [comment removed for export] *)
  Lemma mis_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_A ()) "PFB,$5.Psp1,$5.Ph1,(4.$43.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps9v,(2.&40.)Ps10v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pv1,(2.&40.)Pv2,(2.&40.)Pv3,(2.&40.)P,(51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VPAR,VMD,VMGF,VSALT,VBUF,Vlo,Vslo,Vbs,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)P,(25.$43.R1?.VMD,(19.$26.(27.R4.)(1=.$26.)))P,(25.$43.R20.VMGF,(19.$26.(27.R4.)(1=.$26.)))P,(25.$43.R21.VSALT,(19.$26.(27.R4.)(1=.$26.)))(40.$43.(21.VR,)(>.$43.VR,VHIA,Vh,)(41.$43.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,R23.)(8.(9.R1>.(22.&40.R25.)Vgp,Vtp,R1=.R1<.R1;.Vsp,(22.&40.R25.)R1:.R19.R18.R17.R16.R15.R14.R13.(22.&40.R26.)R12.R11.R10.R?.R>.(22.&40.R26.)R=.R<.(22.&40.(1<.(44.R26.+3.)(45.(21.VR,))))R;.R:.R9.R8.)VF,(22.&40.+:<434.)Vfc,(;.(2.&40.))R22.(<.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until v3. intros D HMD HMGF HSALT.
    (* [comment removed for export] *)
    zstep.
    first [ replace (Z_to_bv 64 18446744073709542554) with (Z_to_bv 64 (-9062)) by (apply bv_eq; reflexivity)
          | match goal with |- ?g => idtac "MIS-LIT-FORM:" g end ].
    eapply epi_walk with (r := -9062); first [ eassumption | clear; lia | match goal with |- ?g => idtac "MIS-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

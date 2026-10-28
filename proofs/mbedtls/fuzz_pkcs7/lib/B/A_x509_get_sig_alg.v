(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_oid A_oid_sig_alg A_platform_zeroize A_asn1_get_alg_null_A A_pkcs7_cinfo
     A_x509_rsassa_pss_A A_x509_rsassa_pss.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
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
Ltac2 gd_tbl_A_x509_get_sig_alg () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "X509_SIG_ALG_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "X509_SIG_ALG_FFR"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "X509_SIG_ALG_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "x509_sig_alg_postA"; "stdpp.bitvector.definitions.bv_swrap"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "A_X509_GET_SIG_ALG"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_rt_hyps"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_x509_rsassa_pss_A.A_SMALLOC_2P"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.A_SMALLOC_1"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.A_AMEMSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_platform_zeroize.A_WRAP_MEMSET"; "x509_sig_alg_stmtA"].


Definition A_X509_GET_SIG_ALG : Z := 0x0ae030.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition X509_SIG_ALG_STACK_A : Z := 4448.
(* [comment removed for export] *)
Definition X509_SIG_ALG_PHI : Z := 2 * 8 + AVOL_CALL + AVOL_CALL.
Definition X509_SIG_ALG_FFR (d : Z) : Z := fr_charge d + fr_charge 28.

Definition x509_sig_alg_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (MD PK OPTS o0 lo slo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig_alg ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O21.O20.O1?.)Lh',(5.O21.O20.O1?.)(1.$6.Lr,$6.(1.(7.$8.)LLB',(7.$8.)(1.$6.Lo,$6.(1.(2.&40.)Lv1,(2.&40.)(1.(2.&40.)Lv2,(2.&40.)(9.(:.$0.R18.(;.(<.(=.O1;.O1:.O19.O18.R17.R16.R15.O17.O16.R14.R13.R12.R11.R10.R?.R>.R=.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R<.R;.R:.R9.)O;.(>.O1;.)O:.(?.(2.&40.))R8.(10.O21.))R7.))(9.(:.(2.&40.)R14.(11.&40.R5.))(9.(9.(12.-3000.R5.)(13.R5.=))(9.(14.O21.R8.)(9.(15.O21.R8.O5.(16.&40.O1:.))(9.(17.O21.(18.O20.)R8.O4.(16.&40.O1:.))(9.(19.O1.R7.)(9.(1:.O21.O20.O1=.O1<.(16.&40.O1:.)(16.&40.O1:.)(1;.O21.O20.O1?.O1>.)(1<.(1=.$6.$6.)(1>.$6.$6.O9.(1?.O9.+4.))(1<.(1=.$6.$6.)(1>.$6.$6.O8.(1?.O8.+4.))(1<.(1=.$6.$6.)(1>.$6.$6.O7.(1?.O7.+8.))(20.(1=.$6.$6.)))))O2.R8.)(9.(:.$6.(21.O21.O20.O1?.R6.)(21.O21.O20.O1?.O1>.))(9.(:.$6.(1;.O21.O20.O1?.R6.)(1;.O21.O20.O1?.O1>.))(9.(:.$6.(22.O21.O20.O1?.R6.)(22.O21.O20.O1?.O1>.))(9.(23.O21.O20.O1?.R6.R7.)(9.Px,$6.P,(24.O21.O20.O1?.O1>.R1.)(24.O21.O20.O1?.R8.R2.)(9.(13.(25.O21.O20.O1?.R6.)(1?.(25.O21.O20.O1?.O1>.)$26.))(9.(13.(27.O21.O20.O1?.R6.)(1?.(27.O21.O20.O1?.O1>.)(28.O3.)))(9.(29.O21.R8.O9.(1<.$2:.(2;.R2.)(20.$2:.)))(9.(29.O21.R8.O8.(1<.$2:.(2;.R1.)(20.$2:.)))(9.(29.O21.R8.O7.(1<.$2:.(2<.(11.&40.R3.))(20.$2:.)))(9.(2=.O21.O20.O1?.R6.R4.O1<.R8.)(2>.(9.(:.(7.$8.)R4.O1=.)(:.$6.R3.O6.))(9.(:.$6.R5.=)(9.(:.(7.$8.)R4.(1<.(1=.$6.$6.)(1>.$6.$6.R3.+8.)O1=.))(9.(:.$6.(2?.R3.+10.)=)(9.(30.O20.O1=.O1<.R3.+8.)(2>.(13.(1?.R3.+8.)(31.O20.))(13.(1;.O21.O20.O1?.O1>.)R3.)))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_sig_alg_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig_alg ()) "Ph,(5.O4.O3.O2.)PLB,(7.$8.)PLF,(7.$8.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(32.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.POID,$6.POP,$6.POLEN,$6.PPAR,$6.PMD,$6.PPK,$6.POPTS,$6.PBUF,$6.Ppp,$6.Po0,$6.Plo,$6.Pslo,$6.Pd,$6.Poxs,(7.(2.&8.))Pbs,(7.(2.&8.))Potg,(2.&40.)Popd,(2.&40.)Pptag,(2.&40.)Pppad,(2.&40.)Pplen,(2.&40.)Pv1,(2.&40.)Pv2,(2.&40.)P,(2=.O4.O3.O2.R3<.R3;.R3:.R18.)P,(23.O4.O3.O2.R3=.R18.)P,(33.(34.$8.R3<.)#1??.)P,(29.O4.R1;.R19.(35.R:.R9.R17.R18.))P,(36.O4.R1<.R19.R=.)P,(:.$6.(37.(34.(2.&8.)R>.))R19.)P,(29.O4.R1>.R19.(1<.$2:.(2;.R;.)(1<.$2:.(2;.R:.)(1<.$2:.(2<.R9.)(1<.$2:.(2<.(11.&40.R14.))(20.$2:.))))))P,(36.O4.R1?.R16.R?.)P,(2>.(9.(:.$6.R16.=)(:.$6.(16.&40.R;.)=))(9.(13.R17.R16.)(13.(1?.R16.(16.&40.R;.))(1?.R17.(37.(34.(2.&8.)R10.))))))P,(13.(1?.(1?.R18.(37.(34.(2.&8.)R11.)))+8.)(38.+2.+2?.))P,(13.(1?.(1?.R1?.R1>.)+8.)(38.+2.+2?.))P,(29.O4.R23.R1=.(1<.$2:.(2;.R=.)(20.$2:.)))P,(29.O4.R24.R1=.(1<.$2:.(2;.R=.)(20.$2:.)))P,(29.O4.R25.R1=.(1<.$2:.(2<.(11.&40.R1:.))(20.$2:.)))P,(2>.(13.(1?.R20.+4.)R1?.)(13.(1?.R1?.+4.)R20.))P,(2>.(13.(1?.R21.+4.)R1?.)(13.(1?.R1?.+8.)R21.))P,(2>.(13.(1?.R21.+4.)R20.)(13.(1?.R20.+8.)R21.))P,(2>.(13.(1?.R23.+4.)R27.)(13.(1?.R27.+18.)R23.))P,(2>.(13.(1?.R23.+4.)R28.)(13.(1?.R28.+18.)R23.))P,(2>.(13.(1?.R25.+4.)R28.)(13.(1?.R28.R27.)R25.))P,(2>.(13.(1?.R25.+4.)R29.)(13.(1?.R29.R28.)R25.))P,(2>.(13.(1?.R27.+4.)R28.)(13.(1?.R28.+18.)R27.))P,(2>.(13.(1?.R27.+4.)R29.)(13.(1?.R29.+18.)R27.))P,(2>.(13.(1?.R27.+8.)R2:.)(13.(1?.R2:.+18.)R27.))P,(2>.(:.$6.(37.(34.(2.&8.)R20.))=)(2>.(13.(1?.R2:.+4.)R27.)(13.(1?.R27.(37.(34.(2.&8.)R20.)))R2:.)))P,(2>.(:.$6.(37.(34.(2.&8.)R21.))=)(2>.(13.(1?.R2:.+4.)R28.)(13.(1?.R28.(37.(34.(2.&8.)R21.)))R2:.)))P,(2>.(:.$6.(37.(34.(2.&8.)R22.))=)(2>.(13.(1?.R2:.+8.)R29.)(13.(1?.R29.(37.(34.(2.&8.)R22.)))R2:.)))P,(:.$6.(2?.R31.+8.)=)P,(:.$6.(2?.R2?.+8.)=)P,(:.$6.(2?.R2?.+4.)=)P,(:.$6.(2?.R2?.+4.)=)P,(:.$6.(2?.R2?.+8.)=)P,(9.(12.=R36.)(13.(1?.R36.+18.)(38.+2.+40.)))P,(12.=R36.)P,(9.(12.=R35.)(13.(1?.R35.+18.)(38.+2.+40.)))P,(9.(12.=R35.)(13.(1?.R35.+4.)(38.+2.+40.)))P,(9.(12.=R35.)(13.(1?.R35.+4.)(38.+2.+40.)))P,(9.(12.=R35.)(13.(1?.R35.+8.)(38.+2.+40.)))P,(12.=R35.)P,(9.(13.=R34.)(12.R34.(38.+2.+40.)))P,(15.O4.R40.R34.(16.&40.R60.))P,(17.O4.(18.O3.)R41.R34.(16.&40.R61.))P,(13.R36.(39.(16.&40.R62.)$3:.))P,(13.R37.(39.(39.(16.&40.R63.)+160.)(3;.O3.)))P,(13.=(3;.O3.))P,(13.R39.(39.(39.(16.&40.R65.)+220.)(3<.O3.)))P,(13.=(3<.O3.))P,(13.R3;.(39.(39.(16.&40.R67.)+1:0.)(3=.O3.)))P,(13.=(3=.O3.))P,(13.R3=.(39.(39.(16.&40.R69.)+40.)(3>.O3.)))P,(13.=(3>.O3.))P,(13.R3?.(39.(39.(16.&40.R6;.)+40.)(3?.O3.)))P,(13.=(3?.O3.))P,(13.(31.O3.)R40.)P,(13.R41.R42.)P,(:.$6.(2?.(16.&40.R6?.)+10.)=)P,(13.(16.&40.R70.)(21.O4.O3.O2.R74.))P,(13.(16.&40.R71.)(38.+2.+2?.))P,(2>.(13.(1?.R50.+18.)R46.)(13.(16.&40.R72.)R50.))P,(2>.(13.(1?.R50.R4?.)R47.)(13.(16.&40.R73.)R50.))P,(2>.(13.(1?.R4?.+18.)R48.)(13.(16.&40.R74.)R4?.))P,(13.(1?.R4?.+4.)R49.)P,(13.(1?.R4?.+4.)R4:.)P,(13.(1?.R4?.+8.)R4;.)P,(2>.(:.$6.(37.(34.(2.&8.)R48.))=)(2>.(13.(1?.R4?.(37.(34.(2.&8.)R48.)))R4<.)(13.(16.&40.R78.)R4?.)))P,(40.(41.O3.)(42.$8.R7<.(43.R7;.))R4=.R54.+18.)P,(40.(41.O3.)(42.$8.R7=.(43.R7<.))R4>.R54.+4.)P,(40.(41.O3.)(42.$8.R7>.(43.R7=.))R4?.R54.+4.)P,(40.(41.O3.)(42.$8.R7?.(43.R7>.))R50.R54.+8.)P,(40.(41.O3.)(42.$8.R80.(43.R7?.))R51.R54.(37.(34.(2.&8.)R4=.)))P,(44.(41.O3.)(42.$8.R81.(43.R80.))R52.(21.O4.O3.O2.R82.)R58.+4.)P,(44.(41.O3.)(42.$8.R82.(43.R81.))R53.(21.O4.O3.O2.R83.)R58.+4.)P,(44.(41.O3.)(42.$8.R83.(43.R82.))R54.(21.O4.O3.O2.R84.)R58.+8.)P,(14.O4.R61.)P,(:.(2.&40.)R80.(11.&40.(45.O3.)))P,(46.O4.(18.O3.)(24.O4.O3.O2.R87.)R63.R61.+18.)P,(46.O4.(18.O3.)(24.O4.O3.O2.R88.)R64.R61.R60.)P,(46.O4.(18.O3.)(24.O4.O3.O2.R89.)R65.R60.+18.)P,(46.O4.(18.O3.)(24.O4.O3.O2.R8:.)R66.R60.+4.)P,(46.O4.(18.O3.)(24.O4.O3.O2.R8;.)R67.R60.+4.)P,(46.O4.(18.O3.)(24.O4.O3.O2.R8<.)R68.R60.+8.)P,(46.O4.(18.O3.)(24.O4.O3.O2.R8=.)R69.R60.(37.(34.(2.&8.)R59.)))P,(13.(1?.(25.O4.O3.O2.R8>.)$26.)$47.)P,(48.O4.R6;.(31.O3.)(1;.O4.O3.O2.R8?.)R63.(16.&40.R8;.)R5=.)P,(13.(1?.(27.O4.O3.O2.R90.)(28.R5>.))$49.)P,(:.(2.&40.)R85.(11.&40.R6;.))P,(:.(2.&40.)R85.(11.&40.R69.))P,(:.(2.&40.)R85.(11.&40.R69.))P,(:.(2.&40.)R85.(11.&40.R69.))P,(:.(2.&40.)R85.(11.&40.R69.))(4:.O4.(4;.O4.O3.O2.R96.R95.R94.R93.R92.R91.R90.R8<.R8;.R82.R81.R80.R7?.R7>.R7=.R7<.R7;.R7:.R79.R74.R73.R6<.R6;.R6:.R67.R66.R65.R64.R72.R71.)(;.(<.(=.R93.R92.R91.R90.R8?.R8>.R8=.R8<.R8;.R8:.R89.R88.R87.R86.R85.R84.R83.R82.R81.R80.R7?.R7>.R7=.R7<.R7;.R7:.R79.R78.R77.R76.R75.)R74.(11.&40.O1.)R73.(?.(2.&40.))R72.(10.O4.))R71.))")
(* [comment removed for export] *).

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0xae1d0]).
Local Ltac zchk_new ::= constr:([0xae050; 0xae054; 0xae058; 0xae0b4; 0xae0bc; 0xae0e4; 0xae0ec; 0xae0f0; 0xae0f4; 0xae124; 0xae128; 0xae12c; 0xae15c; 0xae160; 0xae164]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Local Ltac pchk_merge c k HK :=
  lazymatch goal with
  | |- aevtA ?segs _ _ (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
      let d1 := decode_at segs slow in
      lazymatch d1 with
      | Some (OpImm ALU_ADD ?tmp _ _, _) =>
          let pt := eval vm_compute in (bv_key tmp) in
          let d2 := decode_at segs (slow + 4)%Z in
          lazymatch d2 with
          | Some (Branch BC_LT _ ?kr _, _) =>
              let pk := eval vm_compute in (bv_key kr) in
              merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro)
          end
      end
  end;
  [ let Kz := fresh "Kz" in
    if_cases Kz; zify_cond Kz;
    [ zstep; step_to_if;
      lazymatch goal with
      | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
          replace cnd with true by (symmetry; eapply (shadow_slow_takenN c _ k _ HK Kz); qlia); cbv iota
      end;
      apply evtA_done; eexists; eexists; reflexivity
    | apply evtA_done; eexists; eexists; reflexivity ]
  | let ms' := fresh "ms'" in let vk := fresh "vk" in let vt := fresh "vt" in
    intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k ].
Local Tactic Notation "pchk" constr(H) constr(c) constr(n) :=
  let k := fresh "k" in let RD := fresh "RD" in let HK := fresh "HK" in
  shadow_byte H c n as k RD HK;
  zstep; clear RD; step_to_if;
  pchk_merge c k HK.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis CALLOC : arl_calloc R = 0x69484.
  Hypothesis FREE : arl_free R = 0x6947c.
  Hypothesis GSIG : oid_lookup2_stmtA asegs R HIA A_OID_GET_SIG_ALG 128.
  Hypothesis GPSS : x509_pss_stmtA asegs R HIA A_X509_RSASSA_PSS.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (OID OP OLEN PAR MD PK OPTS BUF pp o0 lo slo d : Z) (oxs bs : list byte) (otg opd ptag ppad plen : word).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis HOLEN : Z.of_nat (length oxs) = OLEN.
  Hypothesis HAP : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig_alg ()) "(2>.(9.(:.$6.Vpp,=)(:.$6.(16.&40.Vplen,)=))(9.(13.VBUF,Vpp,)(13.(1?.Vpp,(16.&40.Vplen,))(1?.VBUF,(37.(34.(2.&8.)Vbs,))))))")
(* [comment removed for export] *).
  Hypothesis B47 : BUF + Z.of_nat (length bs) + 8 <= 2^47.
  Hypothesis O47 : OP + OLEN + 8 <= 2^47.
  Hypothesis D12 : MD + 4 <= PK \/ PK + 4 <= MD.
  Hypothesis D13 : MD + 4 <= OPTS \/ OPTS + 8 <= MD.
  Hypothesis D23 : PK + 4 <= OPTS \/ OPTS + 8 <= PK.
  Hypothesis D1O : MD + 4 <= OID \/ OID + 24 <= MD.
  Hypothesis D2O : PK + 4 <= OID \/ OID + 24 <= PK.
  Hypothesis D1Q : MD + 4 <= OP \/ OP + OLEN <= MD.
  Hypothesis D2Q : PK + 4 <= OP \/ OP + OLEN <= PK.
  Hypothesis D1P : MD + 4 <= PAR \/ PAR + 24 <= MD.
  Hypothesis D2P : PK + 4 <= PAR \/ PAR + 24 <= PK.
  Hypothesis D3P : OPTS + 8 <= PAR \/ PAR + 24 <= OPTS.
  Hypothesis D1B : Z.of_nat (length bs) = 0 \/ MD + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MD.
  Hypothesis D2B : Z.of_nat (length bs) = 0 \/ PK + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= PK.
  Hypothesis D3B : Z.of_nat (length bs) = 0 \/ OPTS + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= OPTS.
  Hypothesis ALO_ : OID mod 8 = 0.
  Hypothesis ALP : PAR mod 8 = 0.
  Hypothesis AL1 : MD mod 4 = 0.
  Hypothesis AL2 : PK mod 4 = 0.
  Hypothesis AL3 : OPTS mod 8 = 0.
  Hypothesis OIDB : 0 < OID /\ OID + 24 <= 2^64.
  Hypothesis OP0 : 0 < OP.
  Hypothesis PARB : 0 < PAR /\ PAR + 24 <= 2^64.
  Hypothesis MDB : 0 < MD /\ MD + 4 <= 2^64.
  Hypothesis PKB : 0 < PK /\ PK + 4 <= 2^64.
  Hypothesis OPTSB : 0 < OPTS /\ OPTS + 8 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis O0B : 0 <= o0 < 2^64.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_SIG_ALG_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 352 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLO4 : lo <= bv_unsigned sp - 544 - arl_need_amem R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis SLO5 : lo <= bv_unsigned sp - 416 - arl_need_bcmp R.
  Hypothesis RTB0 : 0 <= arl_need_bcmp R.
  Hypothesis SLO6 : lo <= bv_unsigned sp - 64 - arl_need_malloc R.
  Hypothesis RTM0 : 0 <= arl_need_malloc R.
  Hypothesis SLO7 : lo <= bv_unsigned sp - 64 - arl_need_free R.
  Hypothesis RTF0 : 0 <= arl_need_free R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DSO : OID + 24 <= lo \/ bv_unsigned sp <= OID.
  Hypothesis DSQ : OP + OLEN <= lo \/ bv_unsigned sp <= OP.
  Hypothesis DSP : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS1 : MD + 4 <= lo.
  Hypothesis DS2 : PK + 4 <= lo.
  Hypothesis DS3 : OPTS + 8 <= lo.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CRP : client_range L (LB ++ fdata LF) lo PAR 24.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo MD 4.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo PK 4.
  Hypothesis CR3 : client_range L (LB ++ fdata LF) lo OPTS 8.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MD 4.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PK 4.
  Hypothesis CW3 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) OPTS 8.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  (* [comment removed for export] *)
  Ltac rt_facts hh :=
    pose proof (hcs_ok asegs R HIA hh) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_SIG_ALG_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA hh) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_sig_alg_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD PK OPTS o0 lo slo d m mo).
  Local Notation W := [(MD, MD + 4); (PK, PK + 4); (OPTS, OPTS + 8)].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).

  (* [comment removed for export] *)
  #[using="Type"] Lemma swrap32_errsum' : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig_alg ()) "Pr,$6.Pc,$6.P,(9.(12.-10000.R2.)(13.R2.=))P,(9.(13.(39.(38.+2.+40.)+10000.)R2.)(12.R2.(38.+2.+40.)))(:.$6.(4<.&20.(1?.(2?.R4.+10000000000000000.)R3.))(1?.R4.(39.R3.(38.+2.+40.))))")
(* [comment removed for export] *).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L12283411672.157L14106684376.157L35655538583.7  L36423571333.175L41288976216.157L44866992728.157L48429268312.157L49345641752.174L5145216728.157 L60098763854.6  L8722184664.157 Q15641568614.175Q18364007270.175Q21877861637.175Q27904925317.175Q32653586022.175Q33915848709.175Q3832210565.175 Q39941338501.175Q41154176102.175Q44650594790.175Q51233520870.175Q59840699110.175Q66523986693.175Q9840924165.175 00000U01:01U02A02f03K04004U05:05D05i06>06S06l07E07Z08308L08e09:09O09d0:90:R0:kS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS1R3HIA2sp2lo2hc4TOPc5HTOPcS2LF2sp3OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB3SLOS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS1R2lo3LOSS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp2lo3oxs2bs3LFB3SLO". (* [comment removed for export] *)
  #[using="IMG OID PAR oxs bs LFB SLO SLOS SLOL LOS TOP SPH"] Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig_alg ()) "Phc,(5.$4=.VR,VHIA,)PLBc,(7.$8.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Pr,$6.Po,$6.Pv1,(2.&40.)Pv2,(2.&40.)Pj,(7.(2.&8.))Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(2=.$4=.VR,VHIA,R1>.R1=.VLF,R1<.)P,(23.$4=.VR,VHIA,R1?.R1<.)P,(19.Vmo,R1=.)P,(:.$6.(21.$4=.VR,VHIA,R21.)(21.$4=.VR,VHIA,Vh,))P,(:.$6.(1;.$4=.VR,VHIA,R22.)(1;.$4=.VR,VHIA,Vh,))P,(:.$6.(22.$4=.VR,VHIA,R23.)(22.$4=.VR,VHIA,Vh,))P,Px,$6.P,(24.$4=.VR,VHIA,Vh,R1.)(24.$4=.VR,VHIA,R26.R2.)P,(13.(25.$4=.VR,VHIA,R25.)(1?.(25.$4=.VR,VHIA,Vh,)$26.))P,(13.(27.$4=.VR,VHIA,R26.)(1?.(27.$4=.VR,VHIA,Vh,)(28.Vd,)))P,(4>.$4=.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)(16.&40.Vsp,)(1<.(1=.$6.$6.)(1>.$6.$6.VMD,(1?.VMD,+4.))(1<.(1=.$6.$6.)(1>.$6.$6.VPK,(1?.VPK,+4.))(1<.(1=.$6.$6.)(1>.$6.$6.VOPTS,(1?.VOPTS,+8.))(20.(1=.$6.$6.)))))Vm,R25.)P,(29.$4=.R26.(1?.(16.&40.Vsp,)-40.)(1<.$2:.(4?.#8.R20.)(1<.$2:.(2<.Vs5,)(1<.$2:.(2<.Vs4,)(1<.$2:.(2<.Vs3,)(1<.$2:.(2<.Vs2,)(1<.$2:.(2<.Vs1,)(1<.$2:.(2<.Vs0,)(1<.$2:.(2<.Vra,)(20.$2:.))))))))))P,(15.$4=.R27.Vlo,(1?.(16.&40.Vsp,)-40.))P,(14.$4=.R28.)P,(17.$4=.(18.VR,)R29.Vslo,(16.&40.Vsp,))P,(29.$4=.R2:.VMD,(1<.$2:.(2;.R26.)(20.$2:.)))P,(29.$4=.R2;.VPK,(1<.$2:.(2;.R26.)(20.$2:.)))P,(29.$4=.R2<.VOPTS,(1<.$2:.(2<.(11.&40.R29.))(20.$2:.)))P,(9.(12.-3000.R2;.)(13.R2;.=))P,(2>.(9.(:.(7.$8.)R2?.VLB,)(:.$6.R2;.Vo0,))(9.(:.$6.R2<.=)(9.(:.(7.$8.)R2?.(1<.(1=.$6.$6.)(1>.$6.$6.R2;.+8.)VLB,))(9.(:.$6.(2?.R2;.+10.)=)(9.(30.VR,VLB,VLF,R2;.+8.)(2>.(13.(1?.R2;.+8.)(31.VR,))(13.(1;.$4=.VR,VHIA,Vh,)R2;.)))))))(4:.$4=.(4;.$4=.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VPK,VOPTS,Vo0,Vlo,Vslo,Vd,Vm,Vmo,)(;.(<.(=.R28.(11.&40.(1?.(16.&40.Vsp,)-40.))Vgp,Vtp,R27.R26.R25.R24.R23.(11.&40.R2=.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(11.&40.+:>0<0.)Vfc,(?.(2.&40.))R2?.(10.$4=.))R2>.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HHc HKc MFc HTc HSc HFc HCSc HVc HFRc PRES FR ST MI SS HMD HPK HOPTS RR CASES.
    rt_facts hc.
    assert (TOPc : bv_unsigned sp <= htop asegs R HIA hc) by (rewrite HTc; exact TOP).
    pose proof (hm_top asegs R HIA hc LBc LF mc HHc) as HTOPc.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOPc; lia]).
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ moc (conj HKc (mo_frame_refl moc))).
    (* [comment removed for export] *)
    do 9 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    release_frame FR ST (bv_unsigned sp).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold x509_sig_alg_postA.
    deexists 15. dexists mf, mo9, hc, r, LBc, o, v1, v2.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [exact (mo_frame_trans _ _ _ MFc MF9)|].
    split; [eapply presW_presA; eassumption|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
    split; [exact HVc|]. split; [exact HFRc|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    exact CASES.
    Unshelve. all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Tactic Notation "acallxA_sp" constr(e) tactic3(apptac) :=
    lazymatch goal with
    | |- aevtA ?segs (KF _ ?R ?HIA ?h ?mo0) _ (MS _ _ _ _ _ ?m _) =>
        eapply (aevtA_cut_evtA_KF segs R HIA h mo0);
        [ apptac
        | lazymatch goal with |- forall x, ?P x -> _ => let hd := head_of P in try unfold hd end;
          rewrite ?(unsigned_lit e) by qlia; post_callA segs m ]
    end.


  (* [comment removed for export] *)
  Ltac kz K := try (change 18446744073709551615 with (Z.ones 64) in K); rewrite ?Z.land_ones in K by (clear; lia); rewrite ?unsigned_lit in K by lia.
  Tactic Notation "errsum" constr(RR) string(tag) :=
    first [ rewrite swrap32_errsum' by (clear - RR; lia)
          | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - RR; lia))
          | match goal with |- ?g => idtac tag g end ].
  (* [comment removed for export] *)
  Tactic Notation "epi_entry" constr(FRC0) constr(rv) string(tag) :=
    let mo9 := fresh "mo9" in let HK9 := fresh "HK9" in let MF9 := fresh "MF9" in
    intros mo9 [HK9 MF9];
    eapply epi_walk with (hc := h) (LBc := LB) (r := rv) (o := o0);
      first [ eassumption | reflexivity | exact MF9 | clear; lia | left; split; reflexivity
            | let xq := fresh "xq" in let Hxq := fresh "Hxq" in intros xq Hxq; exact Hxq
            | unfold X509_SIG_ALG_PHI, AVOL_CALL; clear; lia | unfold X509_SIG_ALG_FFR, fr_charge; clear - FRC0; unfold fr_charge in FRC0; lia
            | match goal with |- ?g => idtac tag g end ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0850@C17025492443.192C35982879851.193C54078651059.194D13554616751.172D13554616751.173D17621704186.268D17621704186.269D21311011018.268D29573701954.221D29573701954.222D29573701954.223D29573701954.224D30792031683.266D31348038237.171D32312579055.171D3298559382.268 D35881667587.172D35881667587.173D36672652819.277D37568203942.194D37578706471.171D38263165562.268D38960061382.304D40673887330.221D40673887330.222D40673887330.223D40673887330.224D43074519423.194D43976969634.304D54031806790.304D54924958990.304D55593774334.304D55593774334.305D56000652842.221D56000652842.222D56000652842.223D56000652842.224D59426836089.222D59429060056.266D59439530203.302D60098976974.171D60109196847.277D60109446735.194D64311484648.194D65479605292.277D65662575434.268D66123782456.194D66130025401.171D6649836138.221 D6649836138.222 D6649836138.223 D6649836138.224 D66523788860.302D66534263615.266D66536519838.220D66536519838.221D67958752476.194D7017656944.220 D7017656944.221 D7024130914.222 D7224719222.221 D7224719222.222 D7224719222.223 D7224719222.224 D7982262708.219 D7982262708.222 K13233830524.172K13233830524.173K18292778079.194K19557566604.172K19557566604.173K23943834773.194K26623949079.192K2705005959.277 K27050767289.277K30262421471.192K31953879216.192K40682541851.192K44164039966.172K44164039966.173K44164039966.277K44682559219.277K45357182371.192K45502290449.194K45554856531.277K46570995600.196K51330597281.194K51792814043.194K51792814043.196K61028991672.194K67971742723.194K68382803047.277K6845747416.192 K68499693399.196K752143892.172  K752143892.173  L10472341635.248L11654682326.2  L12283411672.152L13223535884.2  L13301871092.152L14102771561.6  L14106684376.151L14449531176.176L14449540964.173L14940718518.2  L15020507689.3  L15180794546.3  L15756354262.7  L16497608171.2  L1685717371.0   L17646078182.168L18293330070.2  L18299384510.3  L18892377896.7  L19133794878.3  L19551491050.2  L19703748195.3  L20778673363.5  L20968313059.5  L21227290259.6  L22247317965.9  L22254394384.2  L22658091809.0  L23179735426.6  L23944113172.2  L26071006300.0  L26611708295.2  L26892418956.1  L2704805222.2   L27060793788.2  L27469055408.2  L27666008530.2  L27730136135.2  L28201764546.7  L28573888615.14 L28762391469.4  L29402972479.4  L29683107616.2  L30137263712.10 L30148392868.7  L30249839558.2  L30987168532.11 L31480661359.249L31949492949.3  L32570252182.4  L32851658032.2  L33171728963.1  L33306165521.5  L34203261588.4  L34603895532.0  L34786381466.2  L34834568856.6  L35274593126.3  L3551623394.2   L35653441506.7  L35655538624.7  L35915950914.4  L36493796118.7  L36715738693.2  L37084739175.4  L37396162690.3  L38492666657.0  L39076636629.0  L39220637093.0  L39268637205.0  L39332637397.0  L39559629139.2  L39866938505.3  L39887139444.152L39972443039.3  L40281191306.3  L40408671186.2  L40669617035.2  L40699429691.6  L40834179097.154L41156806145.8  L41288976216.152L42212713040.211L4237669342.5   L42438331952.2  L42516590441.6  L42600734082.3  L43059627067.166L44168742175.3  L44692585718.2  L44866992728.152L45068530702.3  L45121032278.177L45121033169.176L45361373626.2  L45502044816.2  L45554655922.2  L45898055924.152L46181618523.4  L46564631400.4  L46769500230.2  L47763467644.1  L4788352140.2   L48132467214.9  L48429268312.152L50790731766.8  L50875064636.3  L51326406072.2  L5145216728.152 L51645550884.3  L51803357987.3  L51805622202.3  L51925114228.152L52627375391.2  L54416818025.6  L547707976.3    L54794112090.5  L55404177816.9  L56255434971.5  L56490198663.1  L57835863895.5  L57933933556.152L58452338099.2  L58589847153.173L58789197907.176L58903895030.2  L59308632045.6  L59427867805.171L60098763854.6  L60206496545.0  L60893098050.5  L61026292825.4  L61847890602.1  L62023228120.3  L62037211595.9  L62255524708.5  L62586339974.3  L62706067774.5  L63132328254.1  L63337662816.2  L63792904030.8  L63865464161.152L63865464161.249L63962036340.151L64009471222.1  L64518071043.1  L64832085037.2  L64883179765.1  L66000499105.0  L66151427842.16 L66617044166.6  L67901217061.3  L67972999906.3  L67996112456.1  L68382741638.2  L68489397167.3  L68496899164.0  L68533714012.0  L68541655767.2  L6858130109.3   L68591578740.2  L68593790308.151L68684956290.4  L696052593.2    L7274816372.152 L742377621.3    L8722184664.152 L9184813717.4   L973128649.0    L9985633938.170 L9998596476.173 O11111501459.194O16983689553.192O17025492443.192O17073199926.194O27265912465.194O30856859121.192O31626452177.196O33127962143.192O36742947361.192O37665825771.194O39061456065.194O39569367915.192O43811764673.194O43849271089.196O44763476673.194O48908010151.194O48908010151.196O54477284881.192O59360894203.192O59686733300.194O60214362017.192O68468835155.194P11643762451.266P14933861491.266P15178191300.267P16501528978.172P16501528978.173P16681462536.266P16683374761.220P16683374761.222P16687748619.302P24444422907.220P24444422907.222P24446679386.266P24457151577.302P31952178707.302P31954285328.266P31956222129.222P32861676789.266P34792271711.266P39559829938.172P39559829938.173P40682152123.266P45065924472.267P45502163377.266P46558836355.221P46558836355.222P46558836355.267P46558836355.303P46560899379.302P46571375664.266P46573305745.220P46573305745.221P46758367619.266P4792773756.172 P4792773756.173 P51330740737.266P51650724673.192P51792814043.194P51804903112.267P52312398489.220P52312398489.222P52314319160.266P52324799547.302P58464922026.194P58891522918.194P62009657533.192P63343552677.266P67913468736.194P68541594166.277P68670353702.266P68672324231.220P68685024293.302Q11091352144.171Q11267650204.171Q11369794822.195Q11369794822.196Q11420127286.302Q11643762451.266Q13561406482.302Q13567695121.266Q14750497308.171Q14933861491.266Q15178191300.267Q15457446739.169Q15457446739.170Q15643324129.168Q15766564435.194Q17221930104.171Q18365925601.169Q18694146040.171Q18805770220.195Q18805770220.196Q18906732778.171Q20568046174.171Q2121264954.170 Q2121264954.274 Q21798041355.171Q21879645826.169Q22712450012.172Q22712450012.173Q23294020585.194Q2467607158.194 Q25157988860.171Q25367112184.171Q25513505925.171Q25513505925.172Q25662358575.171Q25796025454.170Q25796025454.274Q26295627581.191Q26295627581.194Q26944294047.195Q26944294047.196Q27345904985.195Q27345905374.194Q27346281817.195Q27346281817.196Q27723410818.266Q27907200258.169Q29720241019.171Q30043694244.195Q30043694244.196Q30985055127.211Q30987168531.171Q30987329589.194Q31023710134.218Q31228709292.171Q31394594844.171Q32297849198.188Q32324269455.171Q32375247709.195Q32375247709.196Q32655500769.169Q32861676789.266Q33085744232.195Q33085745135.194Q33185036414.171Q33918256002.169Q34792271711.266Q35014437530.171Q35717497884.171Q36438237060.194Q36438511588.277Q36672652819.277Q36674898963.276Q37568203942.194Q38248387216.194Q3830427394.169 Q39939554818.169Q40273243511.222Q40493084881.191Q4065790877.195 Q4065790877.196 Q40682152123.266Q41152393185.169Q41756892067.171Q42124367769.194Q42185440837.191Q42437205100.302Q42439168719.194Q42439443119.172Q42439443119.173Q42439443119.277Q42441544398.218Q43074519423.194Q4312356703.277 Q43879899724.194Q44219719793.273Q44648843873.169Q44650726555.190Q44990612123.172Q44990612123.173Q45065924472.267Q45120181730.171Q45502163377.266Q46758367619.266Q46805612079.302Q47720333170.273Q47724563598.169Q47724772780.170Q47724772780.274Q48507900270.302Q48509900510.221Q48509900510.303Q48511918028.220Q49698585326.170Q49698585326.171Q50790662996.302Q50795040246.222Q50840533351.194Q51235796833.169Q51317948699.194Q51330740737.266Q51513851506.191Q51661219498.194Q51804903112.267Q52621731034.266Q53843498534.274Q53969758199.171Q54616182503.171Q58891395270.266Q59222816123.194Q59222816508.195Q59429060056.266Q59441596267.267Q59843137889.169Q59865321072.172Q59865321072.173Q59865321072.277Q59865603600.194Q60069660349.273Q60073915713.169Q60310898314.193Q60312004492.191Q60312050231.194Q60614453269.170Q60614453269.274Q6150523001.193 Q62182611701.275Q63009389636.171Q63343552677.266Q64069201839.194Q6416456232.171 Q64255486968.171Q64683667846.172Q64683667846.173Q64683667846.277Q64683942374.194Q64834357205.191Q65477391916.276Q65479605292.277Q65891678805.194Q66123782456.188Q66123782456.194Q66127481304.190Q66130466078.191Q66162928518.194Q66222497782.172Q66222497782.173Q66222497782.277Q66522067074.169Q67958752476.194Q67982214317.222Q67994683919.302Q7377275490.171 Q7377275490.172 Q8943626268.191 Q8956025278.188 Q9843367298.168 00000100500901Y03H04:04l04m04n04o05005105205W06<06=07@08R09H09m0:R0:S0:T0:U0:V0:W0:X0;=0;>0;?0;m0<_0=Q0=R0>B0?20?b0@G0@n0AU0BC0CB0D00Dd0EZ0FH0Fm0GR0GS0H?0H@0Hl0Hm0Hn0Ho0I00IU0IV0IW0IX0IY0IZ0I[0I\0I]0I^0JQ0KS0L70Lj0Ml0NG0Na0ON0P70PQ0Pn0QH0R;0S=0Sj0TS0Tm0UH0V40VT0Vm0Vn0WK0X20XV0YB0Y_0Z<0[90\E0\F0\G0\l0\m0]R0]S0^80^b0_L0_M0_X0_Y0_g0_h0_i0`N0`U0`V0`n0a80a90aD0aE0aW0aX0al0am0an0bA0bB0bC0bD0bH0bI0bJ0bT0b\0b]0c40cc0cd0d30d;0d<0d=0d>0de0eL0eM0e[0e\0e_0em0f;0f<0f=0fM0fN0fU0fm0gH0gV0gW0gX0gY0gb0gc0gd0ge0gf0gg0gh0h30hX0hY0hb0hj0hk0i?0if0ig0jL0k]0km0l50l60l@0ll0lm0ln0mS0mT0n>0nh0ni0nj0nk0oP0o^0o_0o`0oa0ob10710\10m11811911^11_11`11a12F12G12H12R12b13613I13J13Z14?14@14e15J15K15U15V15`15a16216316616716L16]16h17<17?17@17[18@18g19L19P19S19[19^19_1:@1:S1:T1:U1:Y1:Z1:[1:\1:]1:^1:_1:k1;V1;e1;m1<R1<S1=81=F1=G1>01>Y1>Z1>[1>f1>g1>h1>i1>j1>k1>l1>m1>n1>o1?01?11?21?31?41?51?61?71?81?91?S1?k1@G1A91B:1BX1C61CT1D21DN1Dj1EF1Eb1F?1F\1G91GQ1Gj1H^1Ia1J;1JW1K21KR1L21LR1M=1M>1M?1M@1MA1MZ1NL1OM1Of1PB1PC1P`1Q<1QX1R41RP1S01SP1Sl1TF1Td1UW1V41VQ1Vn1Vo1W01X51Y:1Y`1Ya1ZG1Zm1Zn1Zo1[01[E1[Z1[o1\K1\L1\a1]71]81]91]:1];1]O1]c1]d1^=1^a1_T1_U1_m1`C1`D1`k1aa1ab1bg1d21dA1dP1dQ1dR1de1e81eK1e^1fG1f`1fa1fb1fc1gN1h91hd1iG1i^1im1j?1j@1jS1jf1k;1k<1kO1kb1kc1l<1l=1lT1lU1ln1m]1nB1ng1o91oK1od20=20T20f20g20h20i21>21?21Q21c22=22W23F24D25425N25`26K26`27427I27[28P29T29U29V29W29X2:>2:R2:f2;:2;N2;m2<L2<k2=J2=i2>H2>g2?F2?[2@02@C2@D2@W2A12A22A[2B82BO2BP2C02CC2CV2Ch2D:2DO2DP2DQ2DR2DS2Dg2E;2EN2Ea2F42F52F62FI2Fl2Fm2Fn2G@2GV2GW2HP2IX2JX2K?2KU2L:2L_2M92MK2M]2Mo2NA2NT2NU2NV2OA2OZ2Ol2P>2PP2Q;2R52RD2RS2RlFS2MDS2PKS1R2LF2ra2sp3OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB4OIDB4PARB3MDB3PKB5OPTSB3SLO3LOS3SPR2HB5Ha_st5Hl_stS1R2LF2sp2s03OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB4OIDB4PARB3MDB3PKB5OPTSB3SLO3LOS3SPR2HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2sp3OID3PAR2MD2PK4OPTS3BUF3oxs2bs3LFB1o3x162HxS2LF2sp3OID3PAR2MD2PK4OPTS3BUF3oxs2bs3LFB1o3x162HxFFFFFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS1R3HIA1h2LF2ra2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3TOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2s03OID3PAR2MD2PK4OPTS3oxs2bs3LFB3TOP2HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFFFFFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1o3x432HxS2LF2sp3OID3PAR2MD2PK4OPTS3BUF3oxs2bs3LFB1o3x432HxS2LF2sp3OID3PAR2MD2PK4OPTS3BUF3oxs2bs3LFB1o3x432HxFS2LF2sp3OID3PAR2MD2PK4OPTS3BUF3oxs2bs3LFB3x302HxS2LF2sp3OID3PAR2MD2PK4OPTS3BUF3oxs2bs3LFB3x302HxS2LF2sp3OID3PAR2MD2PK4OPTS3BUF3oxs2bs3LFB3x302HxS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1oS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1oS1R2LF2sp3OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB3LOSS1R2LF2sp3OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB3LOS1o2HB5Ha_st5Hl_stS1R2LF2sp3OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB3LOSS1R3HIA1h2LF2sp3OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB3TOPS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1o3x162HxS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3x302HxFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3x302HxFFFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFFFFFFFFFS2LF2ra2sp3OID2lo3oxs2bs3LFB3SLO3DSO2HB5Ha_st5Hl_stS2LF2sp2s03OID2lo3oxs2bs3LFB3SLO3DSO2HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2OP4OLEN2MD3oxs2bs3LFB5HOLEN3D1QS2LF2ra2sp3PAR2lo3oxs2bs3LFB3SLO3DSP2HB5Ha_st5Hl_stS2LF2sp2s03PAR2lo3oxs2bs3LFB3SLO3DSP2HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2PK4OPTS3oxs2bs3LFB3D23S2LF3OID2MD3oxs2bs3LFB3D1OS2LF3PAR4OPTS3oxs2bs3LFB3D3P1o2HB5Ha_st5Hl_stS2LF4OPTS3oxs2bs3LFB1o3AP32HB5Ha_st5Hl_stS2LF3PAR2PK3oxs2bs3LFB3D2PS2LF2sp3PAR2lo3oxs2bs3LFB3DSPS2LF3PAR2MD3oxs2bs3LFB3D1PS2LF2ra2sp3BUF2lo3oxs2bs3LFB3SLO3DS42HB5Ha_st5Hl_stS2LF2sp2s03BUF2lo3oxs2bs3LFB3SLO3DS42HB5Ha_st5Hl_st2s12s22s32s42s5S2LF4OPTS3BUF3oxs2bs3LFB3D3B1o2HB5Ha_st5Hl_stS2LF4OPTS3oxs2bs3LFB1o3AP32HB5Ha_st5Hl_stS2LF3OID2PK3oxs2bs3LFB3D2OS2LF2MD4OPTS3oxs2bs3LFB3D13S2LF2PK4OPTS3oxs2bs3LFB3D231o2HB5Ha_st5Hl_stS2LF2sp3BUF2lo3oxs3LFB1l3B473DS4S2LF2MD2PK3oxs2bs3LFB3D12FS2LF2MD3BUF3oxs3LFB1l3B473D1BS2LF2sp2OP4OLEN2lo3oxs2bs3LFB5HOLEN3DSQS2LF2OP4OLEN2PK3oxs2bs3LFB5HOLEN3D2QS2LF2MD4OPTS3oxs2bs3LFB3D131o2HB5Ha_st5Hl_stS2LF2sp3OID2lo3oxs2bs3LFB3DSOS2LF2PK3BUF3oxs3LFB1l3B473D2BS2LF2ra2sp2OP4OLEN2lo3oxs2bs3LFB5HOLEN3SLO3DSQ2HB5Ha_st5Hl_stS2LF2sp2s02OP4OLEN2lo3oxs2bs3LFB5HOLEN3SLO3DSQ2HB5Ha_st5Hl_st2s12s22s32s42s5FFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB4PARBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB4PARBFS3PAR1o3APPFS1R2lo3LOS3ALOFSS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2sp2loFS1R3HIA1h1d4BUDF2h34HFR3S2MD1o3AP1FS3PAR1o3APPFS2sp3BUF2lo2bs3DS4FS1R2lo3LOS3ALO1o3HNCSSS1R3HIA1h1d2h34HFR3FSFS2spFFS3OID4OIDBS2r13Hr1FS1R3HIA1h2h33HV32h43HV4S1R3HIA1h2sp2MD2PK4OPTS2lo3SLO3DS13DS23DS31a2HaFS2sp3OID2lo3DSOS2r13Hr1FFFS1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPRS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1oFS1R2sp2lo4SLO5FS1oS1R2sp2lo4SLO5S1R2sp2lo4SLO3SFS1R3HIA1h1d4BUDFFS2bs2EQS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA2sp2lo2h24TOP25HTOP2S3BUF2bs1o3AP4FFFS1R3HIA1hSSSSSFS2o03O0B2KOS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS1R3HIA1hS2sp3SPHFS1R3HIA1h3BUD2h33HV3S1R2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS1R2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB4OIDB4PARB3MDB3PKB5OPTSB3ACV3SPR1o3HN03HNCS1R3HIA1h1d4FRC0S2MD3MDBFS2MD1o3AP1S2LF2sp3OID3PAR2MD2PK4OPTS2lo3oxs2bs3LFB3SLOFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB4PARBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB4PARBFFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS3BUF2bs1o3AP4FFFFS1R2sp2lo3SLO3LOS3ALOS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS1R2sp2lo3SLO3LOSS2sp2lo3SLOFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFFS1R3HIA2h2S1R3HIA1h2h23HV2S1R2lo3LOS3ALO1o3HNCS2sp2OP4OLEN2lo3DSQFS1R3HIA1h2sp3TOPS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS1o3HN02KNFS1R2lo3LOSSS1R3ACV1o3HN03HNCFS1oFS1R2sp2lo3SLO3LOS3SPRS1R3ACV1o3HN03HNCS2r33Hr32K3S2sp2lo3slo3SLO4SLOLS1oFS1R3HIA1h1d2h34HFR32h44HFR4S2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB1oS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS2bsS1oS2PK3PKBS1oSS2sp2r03SPA1q1r1H2H02q02H41o4HN16S1R3HIA1h1d2h24HFR2FFS2spFFSSFFS4OPTS5OPTSBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB5OPTSBS2sp3PAR2lo3DSPS2sp3SPRS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFBS1R2sp2lo4SLO4SS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3PKBS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3PKBFFS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFS2LF4OPTS3oxs2bs3LFB1o3AP3S2LF2PK3oxs2bs3LFB1o3AP2S2LF3BUF3oxs2bs3LFB1o3AP42NES2LF2ra2sp2PK2lo3oxs2bs3LFB3SLO3DS22HB5Ha_st5Hl_stS2LF2sp2s02PK2lo3oxs2bs3LFB3SLO3DS22HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2sp4OPTS2lo3oxs2bs3LFB3DS3S2LF2sp4OPTS2lo3oxs2bs3LFB3DS3S2LF2sp4OPTS2lo3oxs2bs3LFB3DS3S2LF2sp4OPTS2lo3oxs2bs3LFB3DS3S2LF2sp2MD2lo3oxs2bs3LFB3DS1S2LF2sp2MD2lo3oxs2bs3LFB3DS1S2LF2sp2MD2lo3oxs2bs3LFB3DS1S2LF2sp2MD2lo3oxs2bs3LFB3DS1S2LF2sp3PAR2lo3oxs2bs3LFB3DSPS2LF2sp3PAR2lo3oxs2bs3LFB3DSPS2LF2sp3PAR2lo3oxs2bs3LFB3DSPS2LF2PK3oxs2bs3LFB1o3AP2S2LF3PAR3oxs2bs3LFB1o3APPS2LF2ra2sp4OPTS2lo3oxs2bs3LFB3SLO3DS32HB5Ha_st5Hl_stS2LF2sp2s04OPTS2lo3oxs2bs3LFB3SLO3DS32HB5Ha_st5Hl_st2s12s22s32s42s5S2LF3PAR2MD3oxs2bs3LFB3D1PS2LF3BUF3oxs2bs3LFB1o3AP42NES2LF2MD4OPTS3oxs2bs3LFB3D13S2LF2sp3BUF2lo3oxs2bs3LFB3DS42NES2LF2sp3BUF2lo3oxs2bs3LFB3DS42NES2LF2sp3BUF2lo3oxs2bs3LFB3DS42NES2LF2sp3BUF2lo3oxs2bs3LFB3DS42r33Hr33R3N2NEFFFFS2LF3PAR3oxs2bs3LFB1o3APPS2LF2ra2sp2MD2lo3oxs2bs3LFB3SLO3DS12HB5Ha_st5Hl_stS2LF2sp2s02MD2lo3oxs2bs3LFB3SLO3DS12HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2MD2PK3oxs2bs3LFB3D12S2LF2sp2MD2lo3oxs2bs3LFB3DS1FS2LF2MD3BUF3oxs2bs3LFB3D1B2NES2LF2sp2PK2lo3oxs2bs3LFB3DS2S2LF2sp2PK2lo3oxs2bs3LFB3DS2S2LF2sp2PK2lo3oxs2bs3LFB3DS2S2LF2sp2PK2lo3oxs2bs3LFB3DS2S2LF2sp2PK2lo3oxs2bs3LFB3SLO3DS2S2LF2sp2MD2lo3oxs2bs3LFB3SLO3DS1S2LF2sp2PK2lo3oxs2bs3LFB3DS2S2LF4OPTS3oxs2bs3LFB1o3AP3S2LF2sp4OPTS2lo3oxs2bs3LFB3DS3S2LF2sp4OPTS2lo3oxs2bs3LFB3SLO3DS31o2HB5Ha_st5Hl_stS2LF2sp3PAR2lo3oxs2bs3LFB3DSPS2LF2sp3PAR2lo3oxs2bs3LFB3DSPS2LF2sp3PAR2lo3oxs2bs3LFB3DSPFFS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3ALP4OIDB4PARB3MDB3PKB5OPTSB3SPRS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3ALP4OIDB4PARB3MDB3PKB5OPTSB3SPRS1R3HIA2LF2sp3oxs2bs3LFB2h24TOP25HTOP2FS1R3HIA2LF2sp3oxs2bs3LFB2h24TOP25HTOP2S1R3HIA2LF2sp3oxs2bs3LFB2h24TOP25HTOP2FFFS2LF2sp3oxs2bs3LFB2HBS2LF2sp3oxs2bs3LFB2HBS2LF2sp2lo3oxs2bs3LFBS1R2LF2lo3oxs2bs3LFB3LOS3ALOFS2LF2sp2lo3oxs2bs3LFBS1R2LF3oxs2bs3LFB4IMG'FFFFS2LF4OPTS3oxs2bs3LFBS2LF4OPTS3oxs2bs3LFBFS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2ra2sp3oxs2bs3LFB2HB5Ha_st5Hl_stS2LF2sp2s03oxs2bs3LFB2HB5Ha_st5Hl_st2s12s22s32s42s5FS2LF3PAR3oxs2bs3LFB4PARBS1R2LF3oxs2bs3LFB4IMG'FS2LF2ra2sp2lo3oxs2bs3LFB2HB5Ha_st5Hl_stS2LF2sp2s02lo3oxs2bs3LFB2HB5Ha_st5Hl_st2s12s22s32s42s5FS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3AL34OIDB4PARB3MDB3PKB5OPTSB3SPRS2LF2sp3OID3PAR2MD2PK4OPTS3oxs2bs3LFB3AL34OIDB4PARB3MDB3PKB5OPTSB3SPR1o3HN0S2LF3oxs2bs3LFBS2LF3oxs2bs3LFBFFS2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOS3ALO1o3HNCS2LF2sp2lo3oxs2bs3LFB3SLOFFFS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOS3SPH3ALO3ACVS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOS3SPH3ALO3ACVS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOS3SPH3ALO3ACVS1R3HIA1h2LF2sp3oxs2bs3LFB3TOP4HTOPS1R2LF3oxs2bs3LFB5ALWF'S2LF3oxs2bs3LFBS2LF2PK3oxs2bs3LFBFS2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBFS2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBFS2LF2sp2lo3oxs2bs3LFB3SLOFS1R2LF3oxs2bs3LFB5ALWF'FS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp4OPTS2lo3oxs2bs3LFB3SLO1o2HB5Ha_st5Hl_stS2LF4OPTS3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF4OPTS3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF2MD3oxs2bs3LFBS2LF2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2sp2lo3oxs2bs3LFB3SLOS1R3HIA1h2LF3oxs2bs3LFBS2LF2PK3oxs2bs3LFBFFFS2LF2sp2lo3oxs2bs3LFBFS2LF2MD3oxs2bs3LFBS2LF2PK3oxs2bs3LFBS1R2LF3slo3oxs2bs3LFB4SLOSS1R2LF3slo3oxs2bs3LFB4SLOSS1R2LF2ra2sp3slo3oxs2bs3LFB4SLOS2HB5Ha_st5Hl_stS1R2LF2sp2s03slo3oxs2bs3LFB4SLOS2HB5Ha_st5Hl_st2s12s22s32s42s5S1R2LF4OPTS3slo3oxs2bs3LFB4SLOS1o2HB5Ha_st5Hl_stS1R2LF3slo3oxs2bs3LFB4SLOSS2LF2MD3oxs2bs3LFBS2LF2sp4OPTS2lo3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF2sp2lo3oxs2bs3LFBS2LF4OPTS3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBS2LF2PK3oxs2bs3LFBS1R2LF2ra2sp2lo3oxs2bs3LFB3SLO3LOS3ALO2HB5Ha_st5Hl_stS1R2LF2sp2s02lo3oxs2bs3LFB3SLO3LOS3ALO2HB5Ha_st5Hl_st2s12s22s32s42s5FFFFS1R3HIA1h2LF3oxs2bs3LFB2h22h34Estk3HS3S2LF4OPTS3oxs2bs3LFBS2LF4OPTS3oxs2bs3LFBS2LF4OPTS3oxs2bs3LFBS2LF4OPTS3oxs2bs3LFBS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOSS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOSS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOSS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOSS2LF2sp3oxs2bs3LFB3SPH2HB5Ha_stS2LF2sp3oxs2bs3LFB3SPH2HB5Ha_stS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOSS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOSS2LF2sp2lo3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBFS2LF3PAR3oxs2bs3LFBS2LF2MD2PK4OPTS3oxs2bs3LFBFS1R2LF2sp2lo3oxs2bs3LFB3SLO3LOS3ALO1o3HNCS2LF4OPTS3oxs2bs3LFB5OPTSB2HBS1R2LF3oxs2bs3LFB5ALWF'FS2LF2sp2MD2lo3oxs2bs3LFB3SLO3DS1S2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBS2LF2sp3oxs2bs3LFBS2LF2sp3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFBFFFFS2LF4OPTS3oxs2bs3LFBS2LF4OPTS3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBFFS2LF3PAR3oxs2bs3LFBS2LF4OPTS3oxs2bs3LFB5OPTSB2HB5Ha_stFFS2LF2PK3oxs2bs3LFBS1R2LF3oxs2bs3LFB4IMG'FS1R3HIA1h2LF2ra2sp3slo3oxs2bs3LFB3TOP4HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2s03slo3oxs2bs3LFB3TOP4HTOP2HB5Ha_st5Hl_st2s12s22s32s42s5S1R3HIA2LF2sp4OPTS3slo3oxs2bs3LFB1o2h24TOP25HTOP22HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo3oxs2bs3LFB3TOP4HTOPS2LF2PK3oxs2bs3LFB3PKBS2LF4OPTS3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF4OPTS3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF2MD2PK4OPTS3oxs2bs3LFBS2LF2PK3oxs2bs3LFBS2LF2PK3oxs2bs3LFBS2LF2PK3oxs2bs3LFBS2LF2PK3oxs2bs3LFBS2LF3PAR3oxs2bs3LFBFFS2LF2MD2PK4OPTS3oxs2bs3LFB1o2HB5Ha_st5Hl_stS2LF2sp2lo3oxs2bs3LFB3SLOS2LF2PK3oxs2bs3LFBS2LF2sp3oxs2bs3LFBS2LF2sp3oxs2bs3LFBS2LF2ra2sp2lo3oxs2bs3LFB3SLO2HB5Ha_st5Hl_stS2LF2sp2s02lo3oxs2bs3LFB3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S2LF3oxs2bs3LFBS2LF3oxs2bs3LFBS2LF2sp2lo3oxs2bs3LFB3SLO". (* [comment removed for export] *)
  #[using="IMG CALLOC FREE GSIG GPSS LFB HOLEN HAP B47 O47 D12 D13 D23 D1O D2O D1Q D2Q D1P D2P D3P D1B D2B D3B ALO_ ALP AL1 AL2 AL3 OIDB OP0 PARB MDB PKB OPTSB BUF0 O0B SLO SLO3 RTS0 SLO4 RTA0 SLO5 RTB0 SLO6 SLO7 SLOS SLOL LOS SPA TOP SPH DSO DSQ DSP DS1 DS2 DS3 DS4 CRP CR1 CR2 CR3 CR4 CW1 CW2 CW3 TPV"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig_alg ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pv1,(2.&40.)Pv2,(2.&40.)P,(2=.$4=.VR,VHIA,Vh,VLB,VLF,Vm,)P,(23.$4=.VR,VHIA,Vh,Vmo,)P,(29.$4=.Vm,VOID,(35.Votg,Vopd,VOLEN,VOP,))P,(36.$4=.Vm,VOP,Voxs,)P,(29.$4=.Vm,VPAR,(1<.$2:.(2;.Vptag,)(1<.$2:.(2;.Vppad,)(1<.$2:.(2<.Vplen,)(1<.$2:.(2<.(11.&40.Vpp,))(20.$2:.))))))P,(36.$4=.Vm,VBUF,Vbs,)P,(29.$4=.Vm,VMD,(1<.$2:.(2;.R8.)(20.$2:.)))P,(29.$4=.Vm,VPK,(1<.$2:.(2;.R8.)(20.$2:.)))P,(29.$4=.Vm,VOPTS,(1<.$2:.(2<.(11.&40.Vo0,))(20.$2:.)))P,(15.$4=.Vm,Vlo,(16.&40.Vsp,))P,(17.$4=.(18.VR,)Vm,Vslo,(16.&40.Vsp,))P,(14.$4=.Vm,)P,(46.$4=.(18.VR,)(24.$4=.VR,VHIA,Vh,)Vm,VOID,+18.)P,(46.$4=.(18.VR,)(24.$4=.VR,VHIA,Vh,)Vm,VOP,VOLEN,)P,(46.$4=.(18.VR,)(24.$4=.VR,VHIA,Vh,)Vm,VPAR,+18.)P,(46.$4=.(18.VR,)(24.$4=.VR,VHIA,Vh,)Vm,VMD,+4.)P,(46.$4=.(18.VR,)(24.$4=.VR,VHIA,Vh,)Vm,VPK,+4.)P,(46.$4=.(18.VR,)(24.$4=.VR,VHIA,Vh,)Vm,VOPTS,+8.)P,(46.$4=.(18.VR,)(24.$4=.VR,VHIA,Vh,)Vm,VBUF,(37.(34.(2.&8.)Vbs,)))P,(13.(1?.(25.$4=.VR,VHIA,Vh,)$26.)$47.)P,(48.$4=.Vm,(31.VR,)(1;.$4=.VR,VHIA,Vh,)VOPTS,(16.&40.Vsp,)Vd,)P,(13.(1?.(27.$4=.VR,VHIA,Vh,)(28.Vd,))$49.)(4:.$4=.(4;.$4=.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VPK,VOPTS,Vo0,Vlo,Vslo,Vd,Vm,Vmo,)(;.(<.(=.Vra,Vsp,Vgp,Vtp,R22.R21.R20.Vs0,Vs1,(11.&40.VOID,)(11.&40.VPAR,)(11.&40.VMD,)(11.&40.VPK,)(11.&40.VOPTS,)R1?.R1>.R1=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(11.&40.$50.)Vfc,(?.(2.&40.))Vm,(10.$4=.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until v2. intros HH HKmo HOID HOP HPAR HBUF HMD HPK HOPTS ST SS MI OOID OOP OPAR OMD OPK OOPTS OBUF BUD UW BUDF.
    unfold A_X509_GET_SIG_ALG. unfold X509_SIG_ALG_PHI, AVOL_CALL in BUD. unfold X509_SIG_ALG_FFR in BUDF.
    unfold buf_cells in HOID.   (* [comment removed for export] *)
    assert (CRO : crange CS OPTS 8) by (eapply aobj_crange; exact OOPTS).   (* [comment removed for export] *)
    rt_facts h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (fr_charge_nonneg _ _ _ _ _ _ _ UW) as FRC0.
    pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SLO SPR; lia)) as TOP64.
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
    pose proof (bv_unsigned_in_range 64 plen) as PLR. unfold bv_modulus in PLR. cbn [Z.pow Z.of_N Pos.pow] in PLR.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    (* [comment removed for export] *)
    zstep. carve_frame 64%nat ST.
    do 7 zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    do 5 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KO; zify_cond KO.
    2:{ (* [comment removed for export] *)
      idtac "S-BADINPUT".
      zstep. zstep. zstep.
      first [ replace (Z_to_bv 64 18446744073709541376) with (Z_to_bv 64 (-10240)) by (apply bv_eq; reflexivity)
            | match goal with |- ?g => idtac "S-BADINPUT-LIT-FORM:" g end ].
      epi_entry FRC0 (-10240) "S-BADINPUT-LEFT:". }

    assert (O00 : o0 = 0) by (clear - KO O0B; kz KO; lia).
    clear KO.
    (* [comment removed for export] *)
    do 7 zstep.
    pose proof GSIG as SPS. unfold oid_lookup2_stmtA, A_OID_GET_SIG_ALG, buf_cells in SPS.
    idtac "S-OID-CALL".
    acallxA_sp (bv_unsigned sp + -64)
      (eapply SPS with (h := h) (LB := LB) (LF := LF) (OID := OID) (E1 := MD) (E2 := PK) (P := OP) (LEN := OLEN) (lo := lo)
                       (tg := otg) (pd := opd) (v1 := v1) (v2 := v2) (xs := oxs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
       first [ eassumption | reflexivity | exact LOS | exact HOLEN | exact ALO_ | exact AL1 | exact AL2 | exact OP0 | exact D12 | exact D1O | exact D2O
             | exact D1Q | exact D2Q | exact O47
             | lazymatch goal with
               | |- 0 < OID => clear - OIDB; lia
               | |- 0 < MD => clear - MDB; lia
               | |- 0 < PK => clear - PKB; lia
               | |- lo <= _ - 128 - arl_need_bcmp R => clear - SLO5 RTB0; lia
               | |- _ <= htop _ _ _ _ => clear - TOP; lia
               | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
               | |- OID + 24 <= lo \/ _ => clear - DSO; lia
               | |- MD + 4 <= lo \/ _ => left; exact DS1
               | |- PK + 4 <= lo \/ _ => left; exact DS2
               | |- OP + OLEN <= lo \/ _ => clear - DSQ; lia
               | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
               end
             | match goal with |- ?g => idtac "S-OID-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "S-OID-LEFT:" g end.
    clear SPS.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : r1 = 0 \/ _ |- _ => rename H into Hr1 end. unfold MBEDTLS_ERR_OID_NOT_FOUND in Hr1.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    2:{ (* [comment removed for export] *)
      idtac "S-UNKNOWN".
      zstep. zstep. zstep.
      errsum Hr1 "S-UNKNOWN-FORM:".
      assert (RRu : -0x3000 < r1 + (18446744073709541888 - 2 ^ 64) <= 0) by (clear - Hr1; lia).
      assert (R1R : -46 <= r1 <= 0) by (clear - Hr1; lia). zpre.
      epi_entry FRC0 (r1 + (18446744073709541888 - 2 ^ 64)) "S-UNKNOWN-LEFT:". }
    clear K1 Hr1.
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "S-PK-CHK".
    lazymatch goal with O2 : aobj _ _ _ _ PK 4 |- _ => shadow_byte O2 PK 4 as k2 RD2 HK2 end.
    zstep. clear RD2.
    zstep.
    step_to_if. shadow_merge PK k2 HK2.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases K6; zify_cond K6.
    { (* [comment removed for export] *)
      idtac "S-NOTPSS".
      (* [comment removed for export] *)
      zstep. zstep.
      lazymatch goal with O3 : aobj _ _ _ _ PAR 24 |- _ => pchk O3 PAR 4 end.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases K5; zify_cond K5.
      2:{ (* [comment removed for export] *)
        zstep. if_cases K0; zify_cond K0.
        { (* [comment removed for export] *)
          idtac "S-TAGBAD".
          zstep. zstep. zstep.
          first [ replace (Z_to_bv 64 18446744073709542656) with (Z_to_bv 64 (-8960)) by (apply bv_eq; reflexivity)
                | match goal with |- ?g => idtac "S-TAGBAD-LIT-FORM:" g end ].
          epi_entry FRC0 (-8960) "S-TAGBAD-LEFT:". }
        (* [comment removed for export] *)
        do 6 zstep.
        zstep. if_cases KL; zify_cond KL.
        2:{ idtac "S-LENBAD0".
          zstep. zstep. zstep.
          first [ replace (Z_to_bv 64 18446744073709542656) with (Z_to_bv 64 (-8960)) by (apply bv_eq; reflexivity)
                | match goal with |- ?g => idtac "S-LENBAD0-LIT-FORM:" g end ].
          epi_entry FRC0 (-8960) "S-LENBAD0-LEFT:". }
        (* [comment removed for export] *)
        idtac "S-OK0".
        zstep. zstep.
        epi_entry FRC0 (0) "S-OK0-LEFT:". }
      (* [comment removed for export] *)
      do 6 zstep.
      zstep. if_cases KL; zify_cond KL.
      2:{ idtac "S-LENBAD5".
        zstep. zstep. zstep.
        first [ replace (Z_to_bv 64 18446744073709542656) with (Z_to_bv 64 (-8960)) by (apply bv_eq; reflexivity)
              | match goal with |- ?g => idtac "S-LENBAD5-LIT-FORM:" g end ].
        epi_entry FRC0 (-8960) "S-LENBAD5-LEFT:". }
      idtac "S-OK5".
      zstep. zstep.
      epi_entry FRC0 (0) "S-OK5-LEFT:". }
    idtac "S-PSS".
    clear K6.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 431236 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) OPTS (bv_unsigned sp + -64) d).
    { lazymatch goal with P0 : presW _ _ _ _ _ _ _ _ _ m m1 |- _ => pose proof (presW_presA _ _ _ _ _ _ _ _ _ _ _ P0) as PA1 end.
      eapply (uwc_floor asegs m1 _ _ OPTS (bv_unsigned sp)); [| clear; lia].
      eapply (uwc_presA R LB LF _ _ _ W m m1 OPTS (bv_unsigned sp) d PA1 UW);
        [ clear; lia | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [outside]; clear - Ha DS1 DS2 DS3 SLO; lia | clear - SPR; lia | exact TOP64 ]. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := 1) (sz := 8) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; rewrite ?(unsigned_lit OPTS) by (clear - OPTSB; lia);
        first [ eassumption | reflexivity | exact LOS | exact UW1 | exact TPV
              | lazymatch goal with
                | |- lo <= _ - arl_need_malloc R => clear - SLO6; lia
                | |- _ <= htop _ _ _ _ => clear - TOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- 0 <= _ => clear; lia
                | |- _ < AMAX => unfold AMAX; clear; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold AVOL_CALL; clear - BUD; lia
                | |- hfr _ _ _ _ + fr_charge d <= FR_MAX => unfold fr_charge in *; clear - BUDF FRC0; lia
                | |- win24 _ = true -> _ => c24_lit
                end
              | match goal with |- ?g => idtac "S-CALLOC-PRE-LEFT:" g end ]. }
    clear UW1.
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    match goal with H : stk _ m1 lo _ |- _ => clear H end.
    match goal with H : HM _ _ _ h _ _ m1 |- _ => clear H end.
    idtac "S-CALLOC-TRANSPORT".
    presA_transport HP2. clear HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    (* [comment removed for export] *)
    clear CSOK SB64 SCS0 SCS.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
    repeat match goal with O : aobj _ _ CS m2 _ _ |- _ => apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in O end.
    assert (HV2' : havol asegs R HIA h2 <= havol asegs R HIA h + X509_SIG_ALG_PHI) by (unfold X509_SIG_ALG_PHI, AVOL_CALL in *; clear - HV2; lia).
    assert (HFR2' : hfr asegs R HIA h2 <= hfr asegs R HIA h + X509_SIG_ALG_FFR d) by (unfold X509_SIG_ALG_FFR, fr_charge in *; clear - HFR2; lia).
    destruct CASES as [[E0 HH2] | (o & E0 & HREST)]; match type of E0 with ?v = _ => subst v end.
    - (* [comment removed for export] *)
      idtac "S-ALLOCFAIL".
      pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      zstep. zstep. zstep. zstep.
      first [ replace (Z_to_bv 64 18446744073709541248) with (Z_to_bv 64 (-10368)) by (apply bv_eq; reflexivity)
            | match goal with |- ?g => idtac "S-ALLOCFAIL-LIT-FORM:" g end ].
      intros mo9 [HK9 MF9].
      eapply epi_walk with (hc := h2) (LBc := LB) (r := -10368) (o := o0);
        first [ eassumption | reflexivity | exact MF9 | clear; lia | left; split; reflexivity
              | match goal with |- ?g => idtac "S-ALLOCFAIL-LEFT:" g end ].
    - idtac "S-ALLOCOK".
      ddestruct HREST as (HN16 & HFR & HNS & HH2 & HNEW).
      change (1 * 8) with 8 in HFR, HNS, HH2, HNEW. change (Z.to_nat 8) with 8%nat in HNEW. cbn [repeat] in HNEW.
      pose proof (hm_top asegs R HIA h2 ((o, 8) :: LB) LF m2 HH2) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      assert (HINN : In (o, 8) (((o, 8) :: LB) ++ fdata LF)) by (left; reflexivity).
      pose proof (hm_aobj_block asegs R HIA h2 ((o, 8) :: LB) LF m2 o 8 HH2 (or_introl eq_refl)) as ON.
      dpose HFR as (HN0 & HNC & HND & HNAP).
      assert (SUBN : forall b, In b (LB ++ fdata LF) -> In b (((o, 8) :: LB) ++ fdata LF)) by (intros b Hb; right; exact Hb).
      pose proof (fresh_apart_client R LB LF lo PAR 24 o 8 HFR CRP ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APP.
      pose proof (fresh_apart_client R LB LF lo MD 4 o 8 HFR CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client R LB LF lo PK 4 o 8 HFR CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client R LB LF lo OPTS 8 o 8 HFR CR3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP3.
      pose proof (fresh_apart_client0 R LB LF lo BUF (Z.of_nat (length bs)) o 8 HFR CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN.
      { exfalso. kz KN. clear - KN HN0 HNC ACV. lia. }
      clear KN.
      (* [comment removed for export] *)
      do 5 zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      (* [comment removed for export] *)
      match goal with H : rw_cells _ m3 o [CB 8 _] |- _ => rename H into HNEW3 end.
      lazymatch type of HNEW3 with rw_cells _ _ _ [CB 8 ?zb] =>
        apply (rw_cells_split_CB asegs m3 o [] 8 zb [] [4; 4]%nat) in HNEW3; [| reflexivity] end.
      cbn [mk_CB_cells app firstn skipn] in HNEW3.
      cb4_to_c4 HNEW3 (@nil cell).
      lazymatch type of HNEW3 with rw_cells _ _ _ [?c0; _] => cb4_to_c4 HNEW3 [c0] end.
      chunk_split HNEW3 1%nat HO1 HO2.
      match goal with H : HM _ _ _ h2 _ _ m3 |- _ => rename H into HH3 end.
      match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
      match goal with H : mem_inv _ m3 |- _ => rename H into MI3 end.
      match goal with H : sshad _ _ m3 slo (bv_unsigned sp) |- _ => rename H into SS3 end.
      destruct (sshad_split asegs AL m3 slo (bv_unsigned sp + -64) (bv_unsigned sp) SS3 ltac:(clear - SLO SLOL; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia)) as [SSlo SShi].
      clear SS3.
      match goal with H : rw_cells _ m3 MD [C4 ?w] |- _ => rename H into HMD3; rename w into wmd end.
      match goal with H : rw_cells _ m3 PAR _ |- _ => rename H into HPAR3 end.
      match goal with H : presW _ _ _ _ _ _ _ _ _ m m3 |- _ => rename H into PRES3 end.
      assert (SPR3 : 0 <= bv_unsigned sp + -64 < 2^64) by (clear - SPR SLO LOS ALO ACV; lia).
      pose proof GPSS as SPP. unfold x509_pss_stmtA, A_X509_RSASSA_PSS in SPP.
      idtac "S-PSS-CALL".
      eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo).
      { lazymatch type of HO1 with rw_cells _ _ _ [C4 ?wz1] => lazymatch type of HO2 with rw_cells _ _ _ [C4 ?wz2] =>
        eapply SPP with (h := h2) (LB := (o, 8) :: LB) (LF := LF) (PAR := PAR) (MD := MD) (MGF := o) (SALT := o + 4) (BUF := BUF) (pp := pp)
                        (lo := lo) (slo := slo) (bs := bs) (ptag := ptag) (ppad := ppad) (plen := plen) (v1 := wmd) (v2 := wz1) (v3 := wz2) end end;
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by exact SPR3;
          first [ exact HH3 | exact HPAR3 | exact HMD3 | exact HO1 | exact HO2 | exact ST3 | exact SSlo | exact MI3 | exact HAP | exact B47 | exact D1P | exact D1B
                | exact ALP | exact AL1 | exact PARB | exact MDB | exact BUF0 | exact RTS0 | exact RTA0 | exact RTB0 | exact SLOS | exact SLOL | exact TPV | exact LFB
                | reflexivity
                | lazymatch goal with
                  | |- bytes_at _ _ _ _ => eassumption
                  | |- MD + 4 <= o \/ _ => clear - AP1; lia
                  | |- MD + 4 <= o + 4 \/ _ => clear - AP1; lia
                  | |- o + 4 <= o + 4 \/ _ => left; clear; lia
                  | |- o + 4 <= PAR \/ _ => clear - APP; lia
                  | |- o + 4 + 4 <= PAR \/ _ => clear - APP; lia
                  | |- _ = 0 \/ o + 4 <= BUF \/ _ => clear - AP4; lia
                  | |- _ = 0 \/ o + 4 + 4 <= BUF \/ _ => clear - AP4; lia
                  | |- o mod 4 = 0 => clear - HN16; Z.div_mod_to_equations; lia
                  | |- (o + 4) mod 4 = 0 => clear - HN16; Z.div_mod_to_equations; lia
                  | |- 0 < o /\ _ => clear - HN0 HNC ACV; lia
                  | |- 0 < o + 4 /\ _ => clear - HN0 HNC ACV; lia
                  | |- lo <= _ - X509_PSS_STACK_A => unfold X509_PSS_STACK_A; clear - SLO; lia
                  | |- lo <= _ - 288 - _ => clear - SLO3; lia
                  | |- lo <= _ - 480 - _ => clear - SLO4; lia
                  | |- lo <= _ - 352 - _ => clear - SLO5; lia
                  | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                  | |- _ <= htop _ _ _ _ => rewrite HT2; clear - TOP; lia
                  | |- _ <= 2 ^ 47 => clear - SPH; lia
                  | |- PAR + 24 <= lo \/ _ => clear - DSP; lia
                  | |- MD + 4 <= lo \/ _ => left; exact DS1
                  | |- o + 4 <= lo \/ _ => left; clear - HNC ALO LOS; lia
                  | |- o + 4 + 4 <= lo \/ _ => left; clear - HNC ALO LOS; lia
                  | |- _ = 0 \/ BUF + _ <= lo \/ _ => clear - DS4; lia
                  | |- client_range _ _ lo o 4 => apply (client_range_block _ _ _ _ _ _ _ HINN); clear; lia
                  | |- client_range _ _ lo (o + 4) 4 => apply (client_range_block _ _ _ _ _ _ _ HINN); clear; lia
                  | |- client_range _ _ lo PAR 24 => intros aq Haq; destruct (CRP aq Haq) as [X|[X|(bq & Hbq & Hrq)]]; [left; exact X| right; left; exact X| right; right; exists bq; split; [apply SUBN, Hbq| exact Hrq]]
                  | |- client_range _ _ lo MD 4 => intros aq Haq; destruct (CR1 aq Haq) as [X|[X|(bq & Hbq & Hrq)]]; [left; exact X| right; left; exact X| right; right; exists bq; split; [apply SUBN, Hbq| exact Hrq]]
                  | |- client_range _ _ lo BUF _ => intros aq Haq; destruct (CR4 aq Haq) as [X|[X|(bq & Hbq & Hrq)]]; [left; exact X| right; left; exact X| right; right; exists bq; split; [apply SUBN, Hbq| exact Hrq]]
                  | |- client_wrange _ _ lo _ MD 4 => rewrite HT2; eapply client_wrange_mono; [exact CW1| exact SUBN]
                  | |- client_wrange _ _ lo _ o 4 => apply (client_wrange_block _ _ _ _ _ _ _ _ HINN); clear; lia
                  | |- client_wrange _ _ lo _ (o + 4) 4 => apply (client_wrange_block _ _ _ _ _ _ _ _ HINN); clear; lia
                  | |- aobj _ _ _ _ o 4 => eapply aobj_sub; [exact ON| clear; lia| clear; lia]
                  | |- aobj _ _ _ _ (o + 4) 4 => eapply aobj_sub; [exact ON| clear; lia| clear; lia]
                  | |- aobj _ _ _ _ _ _ => eassumption
                  end
                | match goal with |- ?g => idtac "S-PSS-PRE-LEFT:" g end ]. }
      cbv beta. intros ms3 PO. unfold x509_pss_postA in PO.
      ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m4 & h3 & r3 & w1 & w2 & w3
                      & -> & HH4 & Ecs & Etop & Estk & Eflag & Evol & Efr & HKiff & HP4 & MI4 & ST4 & SS4 & Ea0 & Hr3 & HMD4 & HO14 & HO24).
      subst ua0. clear SPP.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      rewrite (unsigned_lit (bv_unsigned sp + -64)) in HP4, ST4, SS4 by exact SPR3.
      (* [comment removed for export] *)
      assert (HPd : presA asegs R LB LF (bv_unsigned sp) (bv_unsigned sp) (hstkhi asegs R HIA h2) [(MD, MD + 4)] m3 m4).
      { eapply (presA_drop_fresh_gen R LB LF _ _ _ [(MD, MD + 4)] o 8 (o + 4) (o + 4 + 4)); [| exact HFR| clear; lia| clear; lia| clear - ALO LOS SLO; lia].
        eapply (presA_drop_fresh_gen R LB LF _ _ _ [(o + 4, o + 4 + 4); (MD, MD + 4)] o 8 o (o + 4)); [| exact HFR| clear; lia| clear; lia| clear - ALO LOS SLO; lia].
        eapply (presA_weaken asegs R); [exact HP4| intros b Hb; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        let xx := fresh "xx" in let Hxx := fresh "Hxx" in
        intros xx Hxx; cbn [outside] in Hxx |- *; ddestruct Hxx as (X1 & X2 & X3 & X4); repeat split; assumption. }
      apply (presW_call asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m3 m4 LB LF (bv_unsigned sp) (bv_unsigned sp) (hstkhi asegs R HIA h2) [(MD, MD + 4)]) in PRES3;
        [ | exact HPd | intros b Hb; exact Hb | intros b Hb; exact Hb | clear; lia | clear; lia | rewrite HS2; clear; lia
          | let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; cbn [outside] in Hxx |- *; split; [exact (proj1 Hxx)| exact I] ].
      clear HPd HMD3 HO1 HO2 SSlo MI3 ST3 HH3 ON.
      try match goal with H : abase _ _ m3 |- _ => clear H end.
      repeat match goal with H : rw_cells _ m3 OID _ |- _ => clear H | H : bytes_at _ m3 OP _ |- _ => clear H
                           | H : aobj _ _ _ m3 OID _ |- _ => clear H | H : aobj _ _ _ m3 OP _ |- _ => clear H end.
      idtac "S-PSS-TRANSPORT".
      presA_transport HP4. clear HP4.
      pose proof (sshad_merge asegs AL m4 slo (bv_unsigned sp + -64) (bv_unsigned sp) SS4 ltac:(eassumption) ltac:(clear - SLO SLOL; lia)) as SSm.
      (* [comment removed for export] *)
      assert (HT3 : htop asegs R HIA h3 = htop asegs R HIA h) by (rewrite Etop; exact HT2).
      assert (HS3 : hstkhi asegs R HIA h3 = hstkhi asegs R HIA h) by (rewrite Estk; exact HS2).
      assert (HF3 : hflag asegs R HIA h3 = hflag asegs R HIA h) by (rewrite Eflag; exact HF2).
      assert (HCS3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros xq Hxq; rewrite Ecs; exact (HCS2 xq Hxq)).
      assert (HV3 : havol asegs R HIA h3 <= havol asegs R HIA h + X509_SIG_ALG_PHI) by (rewrite Evol; exact HV2').
      assert (HFR3 : hfr asegs R HIA h3 <= hfr asegs R HIA h + fr_charge d) by (rewrite Efr; exact HFR2).
      (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      { (* [comment removed for export] *)
        idtac "S-PSS-OK".
        assert (R30 : r3 = 0) by (kz K3; clear - K3 Hr3; first [lia | Z.div_mod_to_equations; lia]).
        subst r3.
        assert (CW3n : client_wrange L (((o, 8) :: LB) ++ fdata LF) lo (htop asegs R HIA h3) OPTS 8)
          by (rewrite HT3; eapply client_wrange_mono; [exact CW3| exact SUBN]).
        do 5 zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        intros mo9 [HK9 MF9].
        eapply epi_walk with (hc := h3) (LBc := (o, 8) :: LB) (r := 0) (o := o);
          first [ eassumption | reflexivity | exact MF9 | exact HT3 | exact HS3 | exact HF3 | exact HCS3 | exact HV3 | clear; lia
                | apply (proj2 (HKiff _)); exact HK9
                | unfold X509_SIG_ALG_FFR, fr_charge in *; clear - HFR3; lia
                | right; split; [reflexivity|]; split; [reflexivity|]; split; [exact HN16|]; split; [exact HFR| exact HNS]
                | match goal with |- ?g => idtac "S-PSS-OK-LEFT:" g end ]. }
      (* [comment removed for export] *)
      idtac "S-PSS-ERR".
      assert (R3N : r3 <> 0) by (intros E0; subst r3; apply K3; clear; first [reflexivity | rewrite ?unsigned_lit by lia; reflexivity]).
      clear K3.
      do 3 zstep.
      replace (Z_to_bv 64 431228 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_free R)) by (rewrite FREE; reflexivity).
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      eapply aevtA_call.
      { intros mo1f [HK1f MF1f].
        eapply (heapA_free asegs R HIA) with (h := h3) (LB := (o, 8) :: LB) (LF := LF) (A := o) (n := 8) (lo := lo) (d := 28);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by exact SPR3;
          first [ eassumption | reflexivity | exact LOS | exact TPV
                | lazymatch goal with
                  | |- HK _ _ _ h3 _ => apply (proj2 (HKiff _)); exact HK1f
                  | |- In (o, 8) _ => left; reflexivity
                  | |- lo <= _ - arl_need_free R => clear - SLO7; lia
                  | |- _ <= htop _ _ _ _ => rewrite HT3; clear - TOP; lia
                  | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                  | |- havol _ _ _ _ + AVOL_CALL <= AVOL_MAX => unfold X509_SIG_ALG_PHI, AVOL_CALL in *; clear - HV3 BUD; lia
                  | |- uwc _ _ _ _ _ _ 28 => apply uwc_cap; clear; lia
                  | |- hfr _ _ _ _ + fr_charge 28 <= FR_MAX => unfold fr_charge in *; clear - HFR3 BUDF; lia
                  end
                | match goal with |- ?g => idtac "S-FREE-PRE-LEFT:" g end ]. }
      (intros ms' mo'' dd_H; ddestruct dd_H as (mo1f & [HK1f MF1f] & PO)).
      ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by exact SPR3.
      ddestruct PO as (MI5 & ST5 & MF5 & HP5 & h4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH5).
      cbn [lb_remove fst Z.eqb] in HP5, HH5. rewrite Z.eqb_refl in HP5, HH5.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m6 end.
      rewrite Estk in HP5.   (* [comment removed for export] *)
      match goal with H : stk _ m5 lo _ |- _ => clear H end.
      match goal with H : HM _ _ _ h3 _ _ m5 |- _ => clear H end.
      repeat match goal with H : rw_cells _ m5 o _ |- _ => clear H | H : rw_cells _ m5 (o + 4) _ |- _ => clear H end.
      idtac "S-FREE-TRANSPORT".
      presA_transport HP5. clear HP5.
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ mo'' (conj HK4 (mo_frame_trans _ _ _ MF1f MF5))).
      clear CSOK SB64 SCS0 SCS.
      pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
      (* [comment removed for export] *)
      zstep. zstep.
      intros mo9 [HK9 MF9].
      eapply epi_walk with (hc := h4) (LBc := LB) (r := r3) (o := o0);
        first [ eassumption | reflexivity | exact MF9 | exact Hr3 | left; split; reflexivity
              | (rewrite HT4; exact HT3) | (rewrite HS4; exact HS3) | (rewrite HF4; exact HF3)
              | (let xq := fresh "xq" in let Hxq := fresh "Hxq" in intros xq Hxq; apply HCS4; exact (HCS3 xq Hxq))
              | (unfold X509_SIG_ALG_PHI, AVOL_CALL in *; clear - HV4 HV3; lia)
              | (unfold X509_SIG_ALG_FFR, fr_charge in *; clear - HFR4 HFR3; lia)
              | match goal with |- ?g => idtac "S-PSS-ERR-LEFT:" g end ].
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_x509_get_sig_alg_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig_alg ()) "PR,$51.PHIA,(52.$4=.R1.)P,(53.R2.R1.)P,(:.$6.(54.R3.)+69484.)P,(:.$6.(55.R4.)+6947<.)P,(:.$6.(56.R5.)$57.)P,(:.$6.(58.R6.+2.)$59.)P,(:.$6.(58.R7.+1.)$5:.)P,(:.$6.(5;.R8.)$5<.)P,(:.$6.(5=.R9.)$5>.)P,(13.=(3<.R:.))(5?.$4=.R;.R:.$50.)")
(* [comment removed for export] *).
Proof.
  intros R HIA ORT CAL FRE UARG SM2 SM1 AMS MSI NEED0. pose proof ORT as (IMG & _).
  pose proof (A_oid_get_sig_alg_spec R HIA ORT) as GSIG.
  pose proof (A_x509_rsassa_pss_spec R HIA ORT UARG SM2 SM1 AMS MSI NEED0) as GPSS.
  unfold x509_sig_alg_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.

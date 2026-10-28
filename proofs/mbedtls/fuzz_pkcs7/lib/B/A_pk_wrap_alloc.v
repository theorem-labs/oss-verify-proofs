(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_ecp_keypair_init.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_x509_crt_init A_rsa_init A_ecp_keypair_init.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_pk_wrap_alloc () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RSA_ALLOC_WRAP_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "pk_alloc_wrap_postA"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "ECKEY_ALLOC_WRAP_PHI"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_init.A_AMEMSET_I"; "rsa_alloc_wrap_stmtA"; "A_RSA_ALLOC_WRAP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "eckey_alloc_wrap_stmtA"; "A_ECKEY_ALLOC_WRAP"].


Definition A_RSA_ALLOC_WRAP : Z := 0x0b1f3c.     (* [comment removed for export] *)
Definition A_ECKEY_ALLOC_WRAP : Z := 0x0b22b8.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation RSA_ALLOC_WRAP_STACK_A := 32 (only parsing).
Notation ECKEY_ALLOC_WRAP_STACK_A := 80 (only parsing).
Definition RSA_ALLOC_WRAP_PHI : Z := 2 * 232 + AVOL_CALL.
Definition ECKEY_ALLOC_WRAP_PHI : Z := 2 * 256 + AVOL_CALL.

Definition pk_alloc_wrap_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SZ PHI : Z) (REP : mem -> list blk -> Z -> Prop) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_wrap_alloc ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1?.O1>.O1=.)Lh',(5.O1?.O1>.O1=.)(1.$6.LC,$6.(7.(8.$0.R13.(9.(:.(;.O19.O18.O17.O16.R12.R11.R10.O15.O14.(<.&40.R1.)R?.R>.R=.R<.R;.R:.R9.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R8.R7.R6.R5.)O9.(=.O19.)O8.(>.(2.&40.))R4.(?.O1?.))R3.))(7.(10.O1?.R4.)(7.(11.O1?.R4.O4.(12.&40.O18.))(7.(13.O1.R3.)(7.(14.O1?.O2.R4.)(7.(15.O1?.O1>.O1;.O1:.(12.&40.O18.)(16.O1>.)(17.O1?.O1>.O1=.O1<.)(18.$19.)O2.R4.)(7.(8.$6.(1:.O1?.O1>.O1=.R2.)(1:.O1?.O1>.O1=.O1<.))(7.(8.$6.(17.O1?.O1>.O1=.R2.)(17.O1?.O1>.O1=.O1<.))(7.(8.$6.(1;.O1?.O1>.O1=.R2.)(1;.O1?.O1>.O1=.O1<.))(7.(1<.O1?.O1>.O1=.R2.R3.)(7.Px,$6.P,(1=.O1?.O1>.O1=.O1<.R1.)(1=.O1?.O1>.O1=.R4.R2.)(7.(1>.(1?.O1?.O1>.O1=.R2.)(20.(1?.O1?.O1>.O1=.O1<.)O6.))(7.(1>.(21.O1?.O1>.O1=.R2.)(20.(21.O1?.O1>.O1=.O1<.)(22.O3.)))(23.(7.(8.$6.R1.=)(24.O1?.O1>.O1=.R2.O1;.O1:.R4.))(7.(8.$6.(25.R1.+10.)=)(7.(26.O1>.O1;.O1:.R1.O7.)(7.(23.(1>.(20.R1.O7.)(16.O1>.))(1>.(17.O1?.O1>.O1=.O1<.)R1.))(7.(24.O1?.O1>.O1=.R2.(27.(28.$6.$6.)(29.$6.$6.R1.O7.)O1;.)O1:.R4.)A3.O5.R4.(27.(28.$6.$6.)(29.$6.$6.R1.O7.)O1;.)R1.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_alloc_wrap_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_wrap_alloc ()) "Ph,(5.O4.O3.O2.)PLB,(2:.$2;.)PLF,(2:.$2;.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Plo,$6.Pd,$6.P,(24.O4.O3.O2.R28.R27.R26.R4.)P,(1<.O4.O3.O2.R29.R4.)P,(11.O4.R6.R4.(12.&40.R26.))P,(1>.(16.O3.)R5.)P,(1>.R6.(2=.(2=.(2=.(12.&40.R28.)+20.)(2>.O3.))(2?.O3.)))P,(1>.(12.&40.R29.)(1:.O4.O3.O2.R2=.))P,(8.$6.(25.(12.&40.R2:.)+10.)=)P,(10.O4.R;.)P,(8.(2.&40.)R2:.(<.&40.(30.O3.)))P,(1>.(20.(1?.O4.O3.O2.R31.)$31.)$32.)P,(33.O4.R>.(16.O3.)(17.O4.O3.O2.R32.)(12.&40.R28.)(12.&40.R2>.)R;.)P,(1>.(20.(21.O4.O3.O2.R33.)(22.R<.))$34.)(35.O4.(36.O4.O3.O2.R34.R33.R32.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.+>8.$31.Lm',P,(2.&40.)(3.(2.&8.))LLB',(2:.$2;.)LC,$6.(37.O4.R3.R2.R1.(38.R1.))R>.R=.R10.R?.)(9.(:.(;.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(<.&40.O1.)R11.(>.(2.&40.))R10.(?.O4.))R?.))")
(* [comment removed for export] *).

Definition eckey_alloc_wrap_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_wrap_alloc ()) "Ph,(5.O5.O4.O3.)PLB,(2:.$2;.)PLF,(2:.$2;.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Plo,$6.Pd,$6.P,(24.O5.O4.O3.R28.R27.R26.R4.)P,(1<.O5.O4.O3.R29.R4.)P,(11.O5.R6.R4.(12.&40.R26.))P,(1>.(16.O4.)R5.)P,(1>.R6.(2=.(2=.(2=.(12.&40.R28.)+50.)(2>.O4.))(2?.O4.)))P,(1>.(12.&40.R29.)(1:.O5.O4.O3.R2=.))P,(8.$6.(25.(12.&40.R2:.)+10.)=)P,(10.O5.R;.)P,(8.(2.&40.)R2:.(<.&40.(30.O4.)))P,(1>.(20.(1?.O5.O4.O3.R31.)$39.)$32.)P,(33.O5.R>.(16.O4.)(17.O5.O4.O3.R32.)(12.&40.R28.)(12.&40.R2>.)R;.)P,(1>.(20.(21.O5.O4.O3.R33.)(22.R<.))$34.)(35.O5.(36.O5.O4.O3.R34.R33.R32.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.+100.$39.Lm',P,(2.&40.)(3.(2.&8.))LLB',(2:.$2;.)LC,$6.(1.(2.&40.)Lidpad,(2.&40.)(1.(2.&40.)LpP,(2.&40.)(1.(2.&40.)LpA,(2.&40.)(1.(2.&40.)LpB,(2.&40.)(1.(2.&40.)LpX,(2.&40.)(1.(2.&40.)LpY,(2.&40.)(1.(2.&40.)LpZ,(2.&40.)(1.(2.&40.)LpN,(2.&40.)(1.(2.&40.)Lhpad,(2.&40.)(1.(2.&40.)Lpd,(2.&40.)(1.(2.&40.)LqX,(2.&40.)(1.(2.&40.)LqY,(2.&40.)(1.(2.&40.)LqZ,(2.&40.)(3:.O5.O2.R10.R?.R>.(3;.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))))))))))))))R>.R=.R10.R?.)(9.(:.(;.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(<.&40.O1.)R11.(>.(2.&40.))R10.(?.O5.))R?.))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variable MT : list modp_ent.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis CALLOC : arl_calloc R = 0x69484.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis RSAINIT : rsa_init_stmtA asegs R HIA A_RSA_INIT RSA_INIT_SIZE.
  Hypothesis KPINIT : ecp_keypair_init_stmtA asegs R HIA MT A_ECP_KEYPAIR_INIT.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01Y0@C17025492443.147C20605825831.148D13156179990.87 D31501237935.86 D32770144022.148D34072411257.116D35881667587.86 D35881667587.87 D38861021845.148D60109446735.148D939044794.148  K23023854880.147K45811411506.147K47381498189.147L11774327555.84 L17317924896.7  L19260219809.0  L19460667499.146L19947928356.146L20433961190.82 L21332807421.1  L23028512581.2  L26892418956.1  L29428324939.5  L29765673068.125L30889312663.116L31401241657.143L31401241662.113L32049487064.115L32049487064.142L32049487064.83 L32774781580.119L34144446698.119L35653441506.7  L3830178207.114 L3832291877.144 L40281191306.3  L43059266230.80 L45073256784.5  L45805283240.2  L46748113268.83 L47388280023.3  L49528438569.6  L49530003784.1  L50790580594.7  L547707976.3    L56552377779.115L56552377779.142L56552377779.84 L59308632045.3  L59381076118.2  L60098763854.3  L62018535662.1  L62022717421.7  L62037211595.8  L696052593.2    N20716133971.148N2371994774.148 N28415070343.148N31170017719.148O17025492443.147O29106661976.147O58569406957.147P23023854880.147Q13296972522.84 Q15641191366.144Q15643324129.82 Q15643598972.114Q25513505925.85 Q25513505925.86 Q3185297965.86  Q32770144022.148Q34423643946.128Q3523383053.128 Q3523544117.86  Q3525463959.103 Q36801578553.86 Q38248387216.148Q3830178207.114 Q3830427394.83  Q3832291877.144 Q38861021845.148Q41836510700.86 Q43666747116.86 Q43879899724.148Q45200632385.128Q45235204093.116Q45914037331.83 Q47883992842.128Q49698585326.84 Q49698585326.85 Q51233929798.144Q51235551740.114Q51235796833.83 Q56868487068.86 Q58146298210.85 Q62700825588.86 Q67438241871.128Q67438535543.86 Q67528989526.86 Q67528989526.87 Q6753771453.86  Q9841299621.144 Q9843086111.114 Q9843367298.82  00000100400g01Z01`01d02F02h02n03=03S03T04;04R04V04m04n05405=05A05B05C05G05Y06H06L06R06V06Z06`06d06j07007K07h08K08T09109A09B09F09G09K09O09l0:60::0:@0:D0:N0:U0:_0:b0:e0;F0;N0;[0<80<90<F0<G0<H0<I0<J0<Q0<X0<_0<f0=?0=X0=Y0=\0=o0>X0?A0?j0@U0@Y0A20AK0Ad0Ag0Ah0Ai0B00BG0BH0BO0B`0C10CB0CI0CP0CW0Cj0DU0De0EX0FE0G00G[0G\0H50HN0HgFS1NS1R5NEED05NEEDA2sp2s02lo3LOS3SLO3SPR2HB5Ha_st5Hl_stS1R5NEED05NEEDA2ra2sp2lo3LOS3SLO3SPR2HB5Ha_st5Hl_stS2sp1NS2spS1R3HIA1h2ra2sp3TOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s03TOP2HB5Ha_st5Hl_stS2sp1NS1R2sp2lo3LOS1NS1R3HIA2sp2lo2h23TOP1NFS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO1N3HNCS1R2sp2lo3LOS3ALO1N3HNCS2spS1R2sp2lo3LOS3ALO1N3HNCSS2sp1NS2sp2lo1NS2spFFS2spS1R2lo3LOS3ALO3ACPS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3SPR1N3HN03HNCS2spS2sp1NS2spS2spS2sp1NS2spS2sp1NS2sp1NS1R3HIA1h2sp2lo3TOP4HTOP2h2S1R5NEED05NEEDA2sp2lo3SLO3SPRS1R5NEED05NEEDA2sp2lo3SLO3SPR1N3HN0S1R3HIA1hS1R5NEED05NEEDA2sp2lo3SLO3SPRS1R3HIA1h2h23HV2FS2spFS2spS2spS1R5NEED05NEEDA2sp2lo3LOS3SLOS1R3HIA2h2S2spS2sp1NS2spS1N3HN02KNS2sp2loS1R2lo3LOSS1RS1RS1R5NEED05NEEDA2sp2lo3LOS3SLO3SPRS2sp3SPRS2sp2lo3x291CS1R2sp2lo3LOS3ALO1N3HNC3x291CFS2sp2lo3x291CFFFFS2sp2HBS2sp2loS2sp2loS2sp2loS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_stSS1NS1R5NEED02sp2lo3SLOS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3ACP3SPRS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3ACP3SPRS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3ACP3SPRS1R5NEED05NEEDA2sp2s02lo3SLO2HB5Ha_st5Hl_stS2loS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLOS1NFFS2sp2loS1R2sp2lo3LOS3ALO1N3HNCFS2sp2HBS1R3HIA2sp2h23TOPS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp2loS2sp2loS2sp2loS1R5NEEDA2sp2lo3SLOS1R5NEED05NEEDA2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3HIA1h2sp3TOPS1R5NEED05NEEDA2sp2lo3LOS3SLO3SPA3ALO3ACP3SPR1N3HN0S1R5NEED05NEEDA2sp2lo3LOS3SLO3SPA3ALO3ACP3SPRS1R5NEED05NEEDA2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s02lo3SLO2HB5Ha_st5Hl_stSS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG CALLOC NEED0 NEEDA RSAINIT"] Lemma A_rsa_alloc_wrap_walk : rsa_alloc_wrap_stmtA asegs R HIA A_RSA_ALLOC_WRAP.
  Proof.
    unfold rsa_alloc_wrap_stmtA, A_RSA_ALLOC_WRAP. intros until d.
    intros HH HKmo ST LOS SLO TOP SPA MI TPV BUD UW BUDF.
    pose proof (conj HH I) as HH0.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (fr_charge_nonneg _ _ _ _ _ _ _ UW) as FRC0.
    pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SLO SPR NEED0 NEEDA; lia)) as TOP64.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold RSA_ALLOC_WRAP_PHI in BUD.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := 1) (sz := 232) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by qlia; try eassumption; try reflexivity; try qlia.
      all: try c24_lit.   (* [comment removed for export] *)
      all: try (eapply (uwc_call asegs [(lo, bv_unsigned sp)] m); [exact UW | exact MU0 | repeat constructor; cbn; clear; lia | clear; lia | clear - SPR; lia | exact TOP64]).
      all: try (unfold AMAX; clear; lia).
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    clear MU0.
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2.
    assert (HPX : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [] m m2).
    { eapply presA_trans.
      - eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) m); [exact (proj1 HH0)| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 (hcs asegs R HIA h) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact (proj1 HH0)| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. repeat (apply Forall_cons; [cbn [fst snd]; solve_crange|]). apply Forall_nil.
      - eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SLO NEED0 NEEDA; lia| clear - LOS SLO NEED0 NEEDA; lia| clear; lia| intros y _; exact I]. }
    assert (WMX : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU WM HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear CSOK SB64 SCS0 SCS HTOP. rewrite <- HT2 in TOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_stack asegs R HIA h2) as SCS0.
    destruct CASES as [[E0 HH2] | (N & E0 & HREST)]; match type of E0 with ?v = _ => subst v end.
    - (* [comment removed for export] *)
      pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      release_frame FR ST2 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_alloc_wrap_postA.
      deexists 14. dexists m2, mo9, h2, 0.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split; [exact HPX|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold RSA_ALLOC_WRAP_PHI; clear - HV2; lia|]. split; [exact HFR2|].
      left. split; [reflexivity|]. assumption.
    - (* [comment removed for export] *)
      ddestruct HREST as (HN16 & HFR & HNS & HH2 & HNEW).
      change (1 * 232) with 232 in HFR, HNS, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
      pose proof (hm_top asegs R HIA h2 ((N, 232) :: LB) LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      assert (HINN : In (N, 232) (((N, 232) :: LB) ++ fdata LF)) by (left; reflexivity).
      pose proof (hm_aobj_block asegs R HIA h2 ((N, 232) :: LB) LF m2 N 232 HH2 (or_introl eq_refl)) as ON.
      pose proof (client_wrange_block L (((N, 232) :: LB) ++ fdata LF) (arl_stklo R) (htop asegs R HIA h2) N 232 N 232 HINN ltac:(lia) ltac:(lia)) as CWN.
      dpose HFR as (HN0 & HNC & HND & HNAP).
      assert (APS : N + 232 <= lo \/ bv_unsigned sp <= N) by (clear - HNC ALO LOS; lia).
      pose proof (munch_refl [(lo, bv_unsigned sp); (N, N + 232)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit in KN by (clear - HN0 HNC; pose proof (alloc_ceiling_val R); lia). clear - KN HN0. lia. }
      clear KN.
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof RSAINIT as SPI. unfold rsa_init_stmtA, A_RSA_INIT, RSA_INIT_SIZE in SPI.
      acallxA_sp (bv_unsigned sp + -16)
        (eapply SPI with (h := h2) (LB := (N, 232) :: LB) (LF := LF) (A := N) (lo := lo) (junk := repeat (Z_to_bv 8 0) 232);
         rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by qlia;
         try eassumption; try reflexivity; try qlia;
         first [ clear - APS; lia
               | clear - SLO NEED0 NEEDA; lia
               | clear - SPA; Z.div_mod_to_equations; lia
               | clear - HN16; Z.div_mod_to_equations; lia
               | match goal with |- ?g => idtac "RSAINIT-PRE-LEFT:" g end ]).
      clear SPI.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-RSAINIT:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells _ m3 N _ |- _ => rename H into HZ end.
      match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
      match goal with H : HM _ _ _ h2 _ _ m3 |- _ => rename H into HH3 end.
      change (Z.to_nat 232) with 232%nat in HZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      release_frame FR ST3 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_alloc_wrap_postA.
      deexists 14. dexists m3, mo9, h2, N.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split.
      { eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_drop_fresh asegs R HIA h2 LB LF _ N 232); [| exact HFR| clear - LOS SLO NEED0 NEEDA; lia].
        eapply (presA_weaken asegs R ((N, 232) :: LB) LB LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2)
                  [(N, N + 232)]);
          [| intros b Hb; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below asegs R HIA h2 ((N, 232) :: LB) LF _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R ((N, 232) :: LB) LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (N + 232 - N) with 232 by lia; eapply aobj_crange; exact ON|]. apply Forall_nil. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold RSA_ALLOC_WRAP_PHI; clear - HV2; lia|]. split; [exact HFR2|].
      right. split; [exact HN16|]. split; [exact HFR|]. split; [exact HNS|]. split; [exact HH3|].
      apply rsa_at_of_zero; [exact HZ| exact HN16| exact HN0| left; reflexivity].
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01]0@C17025492443.161C20605825831.162D13156179990.87 D31501237935.86 D32770144022.162D34072411257.116D35881667587.86 D35881667587.87 D42872267541.162D60109446735.162D939044794.162  K23023854880.161K23841128792.161K58952751029.162K66011880735.161L11774327555.84 L13322460011.160L19947928356.160L20433961190.82 L23028512581.2  L23851781314.2  L26385135850.119L26892418956.1  L29428324939.5  L29765673068.125L31401241657.157L31401241662.113L32049487064.115L32049487064.156L32049487064.83 L32774781580.119L32883548320.7  L35653441506.7  L37867421857.0  L3830178207.114 L3832291877.158 L40281191306.3  L43059266230.80 L45073256784.5  L46748113268.83 L49528438569.6  L49530003784.1  L50790580594.7  L547707976.3    L56280697239.116L56552377779.115L56552377779.156L56552377779.84 L58946492975.1  L59308632045.3  L59381076118.2  L60098763854.3  L62018535662.1  L62022717421.7  L62037211595.8  L66005422213.3  L696052593.2    N49710758624.162N51447937846.162N57450737331.162N63424769440.162O17025492443.161O20605825831.162O29106661976.161O58569406957.161P23023854880.161P58952751029.162Q13296972522.84 Q15641191366.158Q15643324129.82 Q15643598972.114Q18430871725.86 Q25513505925.85 Q25513505925.86 Q27157431220.129Q32770144022.162Q34100696159.129Q3523544117.86  Q3523674515.129 Q3525463959.103 Q36801578553.86 Q38248387216.162Q3830178207.114 Q3830427394.83  Q3832291877.158 Q41836510700.86 Q42872267541.162Q43666747116.86 Q43879899724.162Q45235204093.116Q45914037331.83 Q47884153236.129Q49698585326.84 Q49698585326.85 Q51233929798.158Q51235551740.114Q51235796833.83 Q56868487068.86 Q58146298210.85 Q62700825588.86 Q63040235474.129Q67438405329.129Q67438535543.86 Q67528989526.86 Q67528989526.87 Q6753771453.86  Q9841299621.158 Q9843086111.114 Q9843367298.82  00000100200e01X01^01b02D02f03003?03U03V04A04B04]04a04g05005405505605<05@05R06A06G06K06O06U06Y06_07607Q07R07o08R08[09809H09L09P09T0:10:;0:?0:C0:I0:M0:N0:X0:_0:i0:l0:o0;P0;Q0;Y0;f0<30<P0<Q0<R0<S0<T0<U0<V0<W0<^0<e0<l0=30=40=M0=f0>90><0>S0?<0?e0@N0A90A=0AV0Ao0BH0BI0BP0BQ0BX0BY0B`0C10CB0CS0CZ0Ca0Ch0D;0Df0E60EI0F<0Fi0GT0H?0H@0HY0I20IKFFS1R5NEED05NEEDA2sp2s02lo3LOS3SLO3SPR2HB5Ha_st5Hl_stS1R5NEED05NEEDA2ra2sp2lo3LOS3SLO3SPR2HB5Ha_st5Hl_stS2sp1NS2spS1R3HIA1h2ra2sp3TOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s03TOP2HB5Ha_st5Hl_stS2sp1N3EKSS1R2sp2lo3LOS1NS1R3HIA2sp2lo2h23TOP1NFS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO1N3HNC3EKSFS1R2sp2lo3LOS3ALO1N3HNC3EKSS2spS2sp1NS2sp2lo1NS2spFFS2sp1NS2spS1R2lo3LOS3ALO3ACPS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3SPR1N3HN03HNCS2sp1NS2spS2spS2sp1NS2spS2sp1NS1R2sp2lo3LOS3ALO1N3HNCS1R3HIA1h2sp2lo3TOP4HTOP2h2SS1R5NEED05NEEDA2sp2lo3SLO3SPRS1R5NEED05NEEDA2sp2lo3SLO3SPR1N3HN0S1R3HIA1hS1R5NEED05NEEDA2sp2lo3SLO3SPRS1R3HIA1h2h23HV2S2spS2spS2spS1R5NEED05NEEDA2sp2lo3LOS3SLOS1R3HIA2h2S2spS2spS2sp1NS2spFS1N3HN02KNS2sp2loS1R2lo3LOSS1RS1RS1R5NEED05NEEDA2sp2lo3LOS3SLO3SPRFS2sp3SPRS2sp2lo3x421CS2sp2lo3x421CS1R2sp2lo3LOS3ALO1N3HNC3x421CFFFFFFFS2sp2HBS2sp2loS2sp2loS2sp2loSS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_stS1R5NEED02sp2lo3SLOS1NS1R2sp2lo3LOS3ALO1N3HNCS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3ACP3SPRS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3ACP3SPRS1R5NEED05NEEDA2sp2lo3LOS3SLO3ALO3ACP3SPRS1R5NEED05NEEDA2sp2s02lo3SLO2HB5Ha_st5Hl_stS2loS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLOFS1N3EKSFS2sp2loFS2sp2HBS1R3HIA2sp2h23TOPS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp2loS2sp2loS2sp2loS1R5NEEDA2sp2lo3SLOS1R5NEED05NEEDA2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3HIA1h2sp3TOPS2sp3SPR1N4HN163HN0S1R5NEED05NEEDA2sp2lo3LOS3SLO3SPA3ALO3ACP3SPR1N3HN0S1R5NEED05NEEDA2sp2lo3LOS3SLO3SPA3ALO3ACP3SPRS1R5NEED05NEEDA2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s02lo3SLO2HB5Ha_st5Hl_stSS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLOS1R5NEED05NEEDA2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG CALLOC NEED0 NEEDA KPINIT"] Lemma A_eckey_alloc_wrap_walk : eckey_alloc_wrap_stmtA asegs R HIA MT A_ECKEY_ALLOC_WRAP.
  Proof.
    unfold eckey_alloc_wrap_stmtA, A_ECKEY_ALLOC_WRAP. intros until d.
    intros HH HKmo ST LOS SLO TOP SPA MI TPV BUD UW BUDF.
    pose proof (conj HH I) as HH0.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (fr_charge_nonneg _ _ _ _ _ _ _ UW) as FRC0.
    pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SLO SPR NEED0 NEEDA; lia)) as TOP64.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ECKEY_ALLOC_WRAP_PHI in BUD.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := 1) (sz := 256) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by qlia; try eassumption; try reflexivity; try qlia.
      all: try c24_lit.   (* [comment removed for export] *)
      all: try (eapply (uwc_call asegs [(lo, bv_unsigned sp)] m); [exact UW | exact MU0 | repeat constructor; cbn; clear; lia | clear; lia | clear - SPR; lia | exact TOP64]).
      all: try (unfold AMAX; clear; lia).
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    clear MU0.
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2.
    assert (HPX : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [] m m2).
    { eapply presA_trans.
      - eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) m); [exact (proj1 HH0)| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 (hcs asegs R HIA h) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact (proj1 HH0)| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. repeat (apply Forall_cons; [cbn [fst snd]; solve_crange|]). apply Forall_nil.
      - eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SLO NEED0 NEEDA; lia| clear - LOS SLO NEED0 NEEDA; lia| clear; lia| intros y _; exact I]. }
    assert (WMX : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU WM HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear CSOK SB64 SCS0 SCS HTOP. rewrite <- HT2 in TOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_stack asegs R HIA h2) as SCS0.
    destruct CASES as [[E0 HH2] | (N & E0 & HREST)]; match type of E0 with ?v = _ => subst v end.
    - (* [comment removed for export] *)
      pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      release_frame FR ST2 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_alloc_wrap_postA.
      deexists 14. dexists m2, mo9, h2, 0.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split; [exact HPX|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold ECKEY_ALLOC_WRAP_PHI; clear - HV2; lia|]. split; [exact HFR2|].
      left. split; [reflexivity|]. assumption.
    - (* [comment removed for export] *)
      ddestruct HREST as (HN16 & HFR & HNS & HH2 & HNEW).
      change (1 * 256) with 256 in HFR, HNS, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
      pose proof (hm_top asegs R HIA h2 ((N, 256) :: LB) LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      assert (HINN : In (N, 256) (((N, 256) :: LB) ++ fdata LF)) by (left; reflexivity).
      pose proof (hm_aobj_block asegs R HIA h2 ((N, 256) :: LB) LF m2 N 256 HH2 (or_introl eq_refl)) as ON.
      pose proof (client_wrange_block L (((N, 256) :: LB) ++ fdata LF) (arl_stklo R) (htop asegs R HIA h2) N 256 N 256 HINN ltac:(lia) ltac:(lia)) as CWN.
      dpose HFR as (HN0 & HNC & HND & HNAP).
      assert (APS : N + 256 <= lo \/ bv_unsigned sp <= N) by (clear - HNC ALO LOS; lia).
      pose proof (munch_refl [(lo, bv_unsigned sp); (N, N + 256)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit in KN by (clear - HN0 HNC; pose proof (alloc_ceiling_val R); lia). clear - KN HN0. lia. }
      clear KN.
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof KPINIT as SPI. unfold ecp_keypair_init_stmtA, A_ECP_KEYPAIR_INIT, ECP_KEYPAIR_SIZE in SPI.
      pose proof (eq_refl : ECP_KEYPAIR_SIZE = 256) as EKS.
      acallxA_sp (bv_unsigned sp + -16)
        (eapply SPI with (h := h2) (LB := (N, 256) :: LB) (LF := LF) (A := N) (lo := lo) (LBg := (N, 256) :: LB) (junk := repeat (Z_to_bv 8 0) 256);
         rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by qlia;
         try eassumption; try reflexivity; try qlia;
         first [ clear - APS; lia
               | clear - SLO NEED0 NEEDA; lia
               | clear - SPA; Z.div_mod_to_equations; lia
               | clear - HN16; Z.div_mod_to_equations; lia
               | match goal with |- ?g => idtac "KPINIT-PRE-LEFT:" g end ]).
      clear SPI.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-RSAINIT:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : ecp_keypair_at _ _ m3 _ N _ |- _ => rename H into HZ end.
      match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
      match goal with H : HM _ _ _ h2 _ _ m3 |- _ => rename H into HH3 end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      release_frame FR ST3 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_alloc_wrap_postA.
      deexists 14. dexists m3, mo9, h2, N.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split.
      { eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_drop_fresh asegs R HIA h2 LB LF _ N 256); [| exact HFR| clear - LOS SLO NEED0 NEEDA; lia].
        eapply (presA_weaken asegs R ((N, 256) :: LB) LB LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2)
                  [(N, N + 256)]);
          [| intros b Hb; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below asegs R HIA h2 ((N, 256) :: LB) LF _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R ((N, 256) :: LB) LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (N + 256 - N) with 256 by lia; eapply aobj_crange; exact ON|]. apply Forall_nil. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold ECKEY_ALLOC_WRAP_PHI; clear - HV2; lia|]. split; [exact HFR2|].
      right. split; [exact HN16|]. split; [exact HFR|]. split; [exact HNS|]. split; [exact HH3|].
      deexists 13. exact HZ.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_rsa_alloc_wrap_spec : ltac2:(CDefT.buildp (gd_tbl_A_pk_wrap_alloc ()) "PR,$3<.PHIA,(3=.$3>.R1.)P,(3?.(40.R2.))P,(8.$6.(41.R3.)+69484.)P,(8.$6.(42.R4.)$43.)P,(1>.=(2>.R5.))P,(1>.=(2?.R6.))(44.$3>.R7.R6.$45.)")
(* [comment removed for export] *).
Proof. intros. eapply A_rsa_alloc_wrap_walk; eauto. apply A_rsa_init_spec; assumption. Qed.

Lemma A_eckey_alloc_wrap_spec : ltac2:(CDefT.buildp (gd_tbl_A_pk_wrap_alloc ()) "PR,$3<.PHIA,(3=.$3>.R1.)PMT,(2:.$46.)P,(3?.(40.R3.))P,(8.$6.(41.R4.)+69484.)P,(8.$6.(42.R5.)$43.)P,(1>.=(2>.R6.))P,(1>.=(2?.R7.))(47.$3>.R8.R7.R6.$48.)")
(* [comment removed for export] *).
Proof. intros. eapply A_eckey_alloc_wrap_walk; eauto. apply A_ecp_keypair_init_spec; assumption. Qed.

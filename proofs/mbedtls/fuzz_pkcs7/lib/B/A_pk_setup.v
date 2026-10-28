(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_ecp_keypair_init P_pk_wrap_rsa P_pk_wrap_eckey.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_oid A_x509_crt_init A_pk_defs A_pk_wrap_alloc.
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
Ltac2 gd_tbl_A_pk_setup () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "PK_SETUP_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "pk_setup_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_pk_defs.A_RSA_INFO"; "A_PK_SETUP"; "RocqVerifyHarness.AgentSubmission.B.A_pk_defs.A_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_init.A_AMEMSET_I"; "pk_setup_stmtA"].


Definition A_PK_SETUP : Z := 0x0b1858.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation PK_SETUP_STACK_A := 128 (only parsing).
Definition PK_SETUP_PHI : Z := ECKEY_ALLOC_WRAP_PHI.

Definition pk_setup_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (RSAI : Z)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PKA info lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_setup ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1?.O1>.O1=.)Lh',(5.O1?.O1>.O1=.)(1.$6.Lr,$6.(1.$6.LC,$6.(1.$6.LSZ,$6.(7.(8.$0.R15.(9.(:.(;.O17.O16.O15.O14.R14.R13.R12.O13.O12.(<.&40.R3.)R11.R10.R?.R>.R=.R<.R;.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R:.R9.R8.R7.)O7.(=.O17.)O6.(>.(2.&40.))R6.(?.O1?.))R5.))(7.(10.O1?.R6.)(7.(11.O1?.R6.O3.(12.&40.O16.))(7.(13.O1.R5.)(7.(14.O1?.O2.R6.)(7.(15.O1?.O1>.O19.O18.(12.&40.O16.)(16.O1>.)(17.O1?.O1>.O1=.O1:.)(18.(19.$6.$6.)(1:.$6.$6.O5.(1;.O5.+10.))(1<.(19.$6.$6.)))O2.R6.)(7.(8.$6.(1=.O1?.O1>.O1=.R4.)(1=.O1?.O1>.O1=.O1:.))(7.(8.$6.(17.O1?.O1>.O1=.R4.)(17.O1?.O1>.O1=.O1:.))(7.(8.$6.(1>.O1?.O1>.O1=.R4.)(1>.O1?.O1>.O1=.O1:.))(7.(1?.O1?.O1>.O1=.R4.R5.)(7.Px,$6.P,(20.O1?.O1>.O1=.O1:.R1.)(20.O1?.O1>.O1=.R6.R2.)(7.(21.(22.O1?.O1>.O1=.R4.)(1;.(22.O1?.O1>.O1=.O1:.)$23.))(7.(21.(24.O1?.O1>.O1=.R4.)(1;.(24.O1?.O1>.O1=.O1:.)(25.=)))(26.(7.(8.$6.R3.-3?80.)(7.(27.O1?.O1>.O1=.R4.O19.O18.R6.)(28.O1?.R6.O5.(18.$29.(2:.(<.&40.=))(18.$29.(2:.(<.&40.=))(1<.$29.))))))(7.(8.$6.R3.=)(7.(8.$6.(2;.R2.+10.)=)(7.(2<.O1>.O19.O18.R2.R1.)(7.(26.(21.(1;.R2.R1.)(16.O1>.))(21.(17.O1?.O1>.O1=.O1:.)R2.))(7.(27.O1?.O1>.O1=.R4.(18.(19.$6.$6.)(1:.$6.$6.R2.R1.)O19.)O18.R6.)(7.(28.O1?.R6.O5.(18.$29.(2:.(<.&40.O4.))(18.$29.(2:.(<.&40.R2.))(1<.$29.))))(7.P,(8.$6.O4.O1;.)(7.(8.$6.R2.+>8.)(2=.O1?.R7.(18.(19.$6.$6.)(1:.$6.$6.R3.+>8.)O19.)R3.(2>.R3.)))P,(2?.(8.$6.O4.O1;.))(7.(8.$6.R2.+100.)(1.(2.&40.)Lidpad,(2.&40.)(1.(2.&40.)LpP,(2.&40.)(1.(2.&40.)LpA,(2.&40.)(1.(2.&40.)LpB,(2.&40.)(1.(2.&40.)LpX,(2.&40.)(1.(2.&40.)LpY,(2.&40.)(1.(2.&40.)LpZ,(2.&40.)(1.(2.&40.)LpN,(2.&40.)(1.(2.&40.)Lhpad,(2.&40.)(1.(2.&40.)Lpd,(2.&40.)(1.(2.&40.)LqX,(2.&40.)(1.(2.&40.)LqY,(2.&40.)(1.(2.&40.)LqZ,(2.&40.)(30.O1?.O1<.R14.(18.(19.$6.$6.)(1:.$6.$6.R10.+100.)O19.)R10.(31.R10.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pk_setup_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (RSAI : Z) (ECIS : list Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_setup ()) "Ph,(5.O7.O6.O5.)PLB,(32.$33.)PLF,(32.$33.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(34.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPKA,$6.Pinfo,$6.Plo,$6.P,(27.O7.O6.O5.R29.R28.R27.R5.)P,(1?.O7.O6.O5.R2:.R5.)P,(28.O7.R7.R5.(18.$29.(2:.(<.&40.=))(18.$29.(2:.(<.&40.=))(1<.$29.))))P,(8.$6.(2;.R6.+8.)=)P,(35.=R7.)P,(26.(8.$6.R7.O3.)(36.$6.R7.O2.))P,(26.(21.(1;.R9.+10.)R7.)(21.(12.&40.R2;.)R9.))P,(37.O7.(38.O6.)(20.O7.O6.O5.R30.)R<.R:.+10.)P,(39.(3:.O6.)(3;.$33.R30.(3<.R2?.))R9.(1=.O7.O6.O5.R31.)R;.+10.)P,(11.O7.R>.R:.(12.&40.R2>.))P,(21.(16.O6.)R;.)P,(21.R<.(3=.(3=.(3=.(12.&40.R30.)+80.)(3>.O6.))(3?.O6.)))P,(21.(12.&40.R31.)(1=.O7.O6.O5.R35.))P,(8.$6.(2;.(12.&40.R32.)+10.)=)P,(10.O7.R13.)P,(8.(2.&40.)R32.(<.&40.(40.O6.)))P,(21.(1;.(22.O7.O6.O5.R39.)$23.)$41.)P,(21.(1;.(24.O7.O6.O5.R3:.)(25.=))$42.)P,(8.(2.&40.)R2?.(<.&40.R15.))P,(8.(2.&40.)R2?.(<.&40.R15.))(43.O7.(44.O7.O6.O5.O4.O3.R3=.R3<.R3;.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R19.R18.)(9.(:.(;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(<.&40.O1.)R1:.(>.(2.&40.))R19.(?.O7.))R18.))")
(* [comment removed for export] *).

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x0b1940]).
Local Ltac zchk_new ::= constr:([0x0b1874; 0x0b1878; 0x0b187c; 0x0b18c8; 0x0b18cc]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variable MT : list modp_ent.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis RTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis RSAW : rsa_alloc_wrap_stmtA asegs R HIA A_RSA_ALLOC_WRAP.
  Hypothesis ECW : eckey_alloc_wrap_stmtA asegs R HIA MT A_ECKEY_ALLOC_WRAP.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.

  Local Ltac2 Set LiaOrc.tbl := fun () => "03>0@D11189028015.95 D11189028015.96 D13564290403.141D2774095993.126 D35881667587.95 D35881667587.96 D45500527312.128D45500527312.140D50703400392.128D50703400392.140D50703400392.141D60109196847.128D60109196847.140D60109196847.141K3138337932.128 K3138337932.140 K3138337932.141 K64113782398.95 K64113782398.96 L11685632273.11 L11741095640.125L11741095640.133L11741095640.91 L1207681809.1   L12953351448.93 L13700332227.94 L14800215863.133L15756354262.4  L17377155252.4  L18186376865.0  L19354909044.92 L19935441546.124L19947928356.127L19947928356.139L25382082548.92 L25668873010.93 L26892418956.1  L26924648792.125L26924648792.133L26924648792.92 L27905070109.125L27905070109.137L28006807731.133L29010380273.133L29010380273.92 L29428324939.5  L29788790999.82 L31378308326.91 L31392867444.92 L3152797947.2   L35653441506.7  L35935759450.6  L36012194261.92 L37414286068.92 L37796632789.0  L38948636245.0  L39280637297.0  L3959863514.7   L40149296407.126L40281191306.3  L40834179097.94 L43059266230.89 L43442376564.91 L43654564952.125L43654564952.133L43654564952.92 L43909686289.7  L45073256784.5  L45825525979.10 L49628392745.6  L49952869148.91 L50560326147.1  L51229005915.124L51233362421.127L51233362421.139L51709126199.136L51709126206.124L53735823077.123L53735823077.131L547707976.3    L59308630630.3  L59308631400.3  L59499841752.125L59499841752.133L59499841752.92 L60098763854.3  L62018535662.1  L62022717421.7  L62037211595.8  L62383582187.16 L64116126217.2  L65499935772.81 L7510805464.125 L7510805464.133 L7510805464.92  L8929554458.9   L9410944361.4   P25610814625.125P25610814625.126Q10883991967.124Q10883991967.136Q11109677506.95 Q11109761264.94 Q13562048355.140Q14791076917.96 Q14792959895.114Q15641194494.125Q15641194494.137Q15643324129.91 Q15893294284.125Q18028566964.138Q18363861502.125Q18363861502.137Q18365925601.92 Q18694146040.94 Q20414272036.128Q20414272036.140Q20414272036.141Q20414272036.95 Q20414272036.96 Q21798041355.94 Q25157988860.94 Q25513505925.94 Q25513505925.95 Q25604052563.92 Q25604052563.93 Q25662358575.94 Q26574002091.126Q26574002091.138Q26574002091.139Q28119216628.96 Q29312881484.138Q29312881484.93 Q31228709292.94 Q31255363106.138Q31255363106.93 Q31394594844.94 Q32653239550.125Q32653239550.137Q32655500769.92 Q33915929245.125Q33915929245.137Q33918256002.92 Q35014437530.94 Q35717497884.94 Q36171140397.94 Q37426957269.92 Q37429021386.137Q37821600610.94 Q37821600610.95 Q3830427394.92  Q3832294941.125 Q3832294941.137 Q38722865500.95 Q38807819226.96 Q39939554818.92 Q39941750557.125Q39941750557.137Q41638037421.124Q41638037421.136Q42024716493.92 Q42026781138.137Q43909868710.96 Q44648843873.92 Q44650777470.125Q44650777470.137Q44767788171.94 Q45502445776.127Q45502445776.139Q49241094109.94 Q49698585326.93 Q49698585326.94 Q50558264496.138Q50558264496.93 Q50558457234.92 Q50560717965.137Q50701449160.127Q50701449160.139Q50701449160.140Q51233928830.125Q51233928830.137Q51235796833.92 Q53440817419.125Q53440817419.137Q53440894644.124Q53440894644.136Q53969758199.94 Q54520642575.125Q54520642575.137Q57744452505.94 Q58413128502.96 Q63116570093.125Q63116570093.137Q6416456232.94  Q64255486968.94 Q64696564221.126Q65537657969.125Q65537657969.137Q65614050195.95 Q66522067074.92 Q66524131741.125Q66524131741.137Q807981431.96   Q9841302685.125 Q9841302685.137 Q9843367298.91  00000o02702Y02e03O04B04]05:05U06206T07807^08I09<0:10:i0;_0<^0=J0=V0=d0>00>50>I0>Z0>h0?60?C0?D0?P0?_0?n0@?0@K0@W0@[0@g0A50AA0Aj0BY0CT0Cb0Cn0D@0DL0DX0Dd0De0E@0EU0Ei0F50F60F70F80FO0F[0Fd0G20G[0Gg0H30HA0HM0HN0H^0I50I90IN0IS0I_0Ik0J90JG0JS0Jh0K?0KI0KS0K_0Kk0L90LE0LO0LR0LU0M60N00N10N=0NI0NW0Nc0OH0OW0Oi0P;0PD0PM0P[0Pi0QF0R90Rl0S;0SJ0SY0T>0TN0T]0Tl0U;0UK0Ui0VI0Vl0W_0X[0X\0Xl0YM0Z70ZF0ZU0ZV0Zm0[D0[[0\30\Q0\i0]:0]C0]L0]U0]d0^30^B0^c0_D0_e0`60`70`80`A0`J0a=0b90bZ0c;0c\0cj0d?0d`0eA0eb0ek0f40f=0fF0fG0fV0fe0g40gB0gZ0h40h50hN0hg0i00i90iB0iK0ic0j=0jZ0ji0k80kG0kP0kY0kb0kk0l<0lE0lN0l\0l]0m50mS0mc0md0me0n50nE0ng0oH0oi10J11E11f12G12hS1R5NEED05NEEDA2ra2sp3PKA2lo3POS3LOS3SLO3SPR3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA2lo3POS3LOS3SLO3SPR3PKB2HB5Ha_st5Hl_st2s12s22s3S2sp3PKA4info1C3PKB2HB5Ha_st5Hl_stS2sp3PKA3PKBS1R3HIA1h2ra2sp3PKA3TOP3PKB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s03PKA3TOP3PKB2HB5Ha_st5Hl_st2s12s22s3S2sp3PKA3PKB2HB5Ha_st5Hl_stS2sp3PKA1C3PKB2HB5Ha_st5Hl_stS2sp3PKA3PKB2HB5Ha_st5Hl_stS2sp3PKA1C3PKB2HB5Ha_st5Hl_stS2sp3PKA4info1C3PKB2HB5Ha_st5Hl_stS1R2sp3PKA2lo3LOS3PKB2HB5Ha_st5Hl_stS1R2sp3PKA2lo1C3LOS3PKB2HB5Ha_st5Hl_stS1R2sp3PKA4info2lo1C3LOS3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA2lo2SX3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA2lo2SX1C3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA4info2lo2SX3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2ra2sp3PKA2lo2SX3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA2lo2SX3SLO3PKB2HB5Ha_st5Hl_st2s12s22s3S1R3HIA5NEED05NEEDA1h2sp2lo3LOS3SLO3TOP4HTOPS2sp3PKA3PKBS2sp3PKA1C3PKBS2sp3PKA3PKBS3PKAS2sp3PKA4info3PKB2IBS2sp3PKA4info3PKBS2sp3PKA1C3PKBS1R2lo3LOS3ALOS1R3HIA1h3BUDSS2sp3PKA3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo1C3PKBS2sp3PKA3PKBS2sp3PKA3PKBS2spS2sp3PKA3PKBS2sp3PKA1C3PKBS2sp3PKA3PKBS1R5NEED05NEEDA2sp3PKA2lo3POS3SLO3SPR3PKBS1R5NEED05NEEDA2sp3PKA2lo3POS1C3SLO3SPR3PKB3HN0S1R5NEED05NEEDA2sp3PKA2lo3POS1C3LOS3SLO3ALO3SPR3PKB3HN03HNCS2sp3PKA1C3PKBS2sp3PKA3PKBS1R2lo3LOS3ALO3ACPS2sp3PKA3PKBS2sp3PKA3PKBS2sp3PKA3PKBFS1R3HIA1h2sp2lo3TOP4HTOP2h2S2sp3PKA2lo1C3APC3APSS2sp3PKA4info3PKB2IBS2sp3PKA3PKBSSSS1R2sp2lo3LOS3ALO1C3HNCS2sp3PKA3PKBS1R3HIA1hS1R2sp3PKA3PKBS1R5NEED05NEEDA2sp3PKA2lo3POS3SLO3SPR3PKBS2sp3PKA3PKBS2sp3PKA3PKBS2sp3PKA1C3PKBS2sp3PKA3PKBFS1R3HIA1h2h23HV2S3PKA3POS4PK471q1r1H2H0S2spS2sp3PKA3POS3PKB4PK47S3PKAS2sp3PKA3PKBS2sp3PKA3PKBS2sp3PKA1C3PKBS2sp3PKA1C3PKBS2sp3PKA3PKBS2sp3PKA3POS3PKB4PK47S2sp3PKA3POS1C3PKB4PK47S1R3HIA2h2S1C3HN02KCS4info2IB2KIS2sp3PKA3PKBS2sp3PKA1C3PKBS2sp3PKA3PKBS1R2lo3LOSS1RS1RS1R5NEED05NEEDA2sp2lo3LOS3SLO3SPRS1R3HIA5NEED05NEEDA1h2sp3PKA2lo3LOS3SLO3TOP4HTOP4SBLO2Q21QFS2sp3PKA3PKBS2sp3PKA3PKBS2sp3PKA1C3PKBS2sp3PKA3PKBS1R3HIA1h3PKA4SB644HTOP4SBLO5TOP642SHS1R3PKA4SBLO2SHS2sp3PKA2lo2SX3PKBS2sp3PKA2lo2SX3PKBS3PKA3PKBS3PKA3PKBS3PKA4info3PKBS3PKA4info3PKBS3PKA4info3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA2lo3LOS3SLO4SB643SPR4SBLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3LOS3SLO4SB643SPR4SBLO3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS1R5NEED05NEEDA2sp3PKA2lo3LOS3SLO3PKBS3PKA3POS3PKB2HBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS1R3PKA4IMG'3PKBS2sp3PKA2lo3PKB2HB5Ha_st5Hl_stS2sp3PKA2lo1C3PKB2HB5Ha_st5Hl_stS2sp3PKA4info2lo3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2ra2sp3PKA2lo3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA2lo3SLO3PKB2HB5Ha_st5Hl_st2s12s22s3FS1R3PKA4IMG'3PKBS2ra2sp3PKA2lo3PKB2HB5Ha_st5Hl_stS2sp2s03PKA2lo3PKB2HB5Ha_st5Hl_st2s12s22s3S2sp3PKA3PKB2HBS2sp3PKA3PKB2HBFS3PKA3PKB4PK472HB5Ha_stS3PKA3PKB4PK472HB5Ha_stS3PKA3PKB4PK472HB5Ha_stS1R3HIA1h2sp3PKA3TOP3PKBS2sp3PKA3AL83POS1C3SPR3PKB3HN0S2sp3PKA3AL83POS3SPR3PKBS1R3PKA5ALWF'3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R3PKA5ALWF'3PKBFFS3PKA3PKBS3PKA3PKBS1R5NEED05NEEDA2ra2sp3PKA2lo3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA2lo3SLO3PKB2HB5Ha_st5Hl_st2s12s22s3S1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS3PKA4info3PKBS1R2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBFS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS3PKA4info3PKBS3PKA3PKB2HB5Ha_st5Hl_stS3PKA1C3PKB2HB5Ha_st5Hl_stFS2sp3PKA3SPR3PKB2HB5Ha_stS2sp3PKA3SPR3PKB2HB5Ha_stS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKB2HB5Ha_st5Hl_stS3PKA1C3PKB2HB5Ha_st5Hl_stS3PKA4info3PKB2HB5Ha_st5Hl_stS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS1R3PKA5ALWF'3PKBS3PKA3PKBS3PKA3PKBS3PKA4info3PKBFS2sp3PKA3AL83POS3SPR3PKBS2sp3PKA3AL83POS1C3SPR3PKB3HN0S1R3PKA4IMG'3PKBFFS3PKA3POS3PKB2HBS3PKA3POS3PKB2HBS2sp3PKA4info3POS3SPR3PKB2IB5EINF'S1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3POS3LOS3SLO3SPA4SB643SPR4SBLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKB". (* [comment removed for export] *)
  #[using="IMG RTC RSAW NEED0 NEEDA"] Lemma A_pk_setup_rsa : ltac2:(CDefT.buildp (gd_tbl_A_pk_setup ()) "Ph,(5.$45.VR,VHIA,)PLB,(32.$33.)PLF,(32.$33.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(34.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPKA,$6.Pinfo,$6.Plo,$6.P,(27.$45.VR,VHIA,R29.R28.R27.R5.)P,(1?.$45.VR,VHIA,R2:.R5.)P,(28.$45.R7.R5.(18.$29.(2:.(<.&40.=))(18.$29.(2:.(<.&40.=))(1<.$29.))))P,(8.$6.(2;.R6.+8.)=)P,(35.=R7.)P,(8.$6.R7.$46.)P,(26.(21.(1;.R9.+10.)R7.)(21.(12.&40.R2;.)R9.))P,(37.$45.(38.VR,)(20.$45.VR,VHIA,R30.)R<.R:.+10.)P,(39.(3:.VR,)(3;.$33.R30.(3<.R2?.))R9.(1=.$45.VR,VHIA,R31.)R;.+10.)P,(11.$45.R>.R:.(12.&40.R2>.))P,(21.(16.VR,)R;.)P,(21.R<.(3=.(3=.(3=.(12.&40.R30.)+80.)(3>.VR,))(3?.VR,)))P,(21.(12.&40.R31.)(1=.$45.VR,VHIA,R35.))P,(8.$6.(2;.(12.&40.R32.)+10.)=)P,(10.$45.R13.)P,(8.(2.&40.)R32.(<.&40.(40.VR,)))P,(21.(1;.(22.$45.VR,VHIA,R39.)$23.)$41.)P,(21.(1;.(24.$45.VR,VHIA,R3:.)(25.=))$42.)P,(8.(2.&40.)R2?.(<.&40.R15.))P,(8.(2.&40.)R2?.(<.&40.R15.))(43.$45.(44.$45.VR,VHIA,VMT,$46.R3=.R3<.R3;.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R19.R18.)(9.(:.(;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(<.&40.$47.)R1:.(>.(2.&40.))R19.(?.$45.))R18.))")
(* [comment removed for export] *).
  Proof.
    unfold A_PK_SETUP. intros until lo.
    intros HH HKmo HPK AL8 POS EINF SX OBJ CW ST LOS SLO TOP SPA MI TPV BUD BUDF -> ->.
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
    pose proof (art_stk_high asegs R HIA) as SBLO.
    pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SLO SPR NEED0 NEEDA; lia)) as TOP64.
    pose proof (rw_cells_bound _ _ _ _ HPK) as PKB. cbn [cells_size csize Nat.add] in PKB.
    assert (PK47 : PKA + 16 <= 2^47).
    { destruct (hcs_app asegs R HIA h PKA 16 (aobj_crange _ _ _ _ _ _ OBJ) ltac:(lia)) as [[_ Q]|[_ Q]]; [| exact Q].
      destruct (hcs_app asegs R HIA h _ _ SCS0 ltac:(clear - HTOP TOP SLO LOS NEED0 NEEDA; lia)) as [[_ Q2]|[_ Q2]];
        clear - Q Q2 SB64 SBLO HTOP TOP SLO LOS NEED0 NEEDA; lia. }
    assert (SH : 0 <= Z.shiftr PKA 3 < 2^44) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - POS PK47; Z.div_mod_to_equations; lia).
    assert (IB : 0 < info < 2^32) by (clear - EINF; subst info; unfold A_RSA_INFO; lia).
    pose proof EINF as EINF'. unfold A_RSA_INFO in EINF'.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp); (PKA, PKA + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold PK_SETUP_PHI, ECKEY_ALLOC_WRAP_PHI in BUD.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KI; zify_cond KI; [exfalso; clear - KI IB; rewrite ?unsigned_lit in KI by lia; lia|]. clear KI.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HHx : HM _ _ _ h _ LF mx |- _ =>
        pose proof (abase_got _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GOT; pose proof (abase_gsb _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GSB; rewrite (proj1 IMG') in GOT end end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    lazymatch goal with HHx : HM _ _ _ h _ LF m1 |- _ =>
      pose proof (aobj_img asegs _ (hcs asegs R HIA h) m1 (A_RSA_INFO + 72) 8 (hcs_img_cs R HIA h IMG (proj2 (proj2 (proj2 IMG')))) (hm_img_shadow asegs R HIA h _ LF m1 HHx) ltac:(vm_compute; reflexivity)) as OI;
      pose proof (asan_rtc_const m1 (A_RSA_INFO + 72) [Z_to_bv 8 60; Z_to_bv 8 31; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
                    (RTC m1 (hm_rtc asegs R HIA h _ LF m1 HHx)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB end.
    cbn [length] in TB. rewrite <- EINF in OI, TB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. try (if_cases KF; zify_cond KF; [exfalso; revert KF; clear; intros KF; rewrite ?unsigned_lit in KF by lia; cbn in KF; lia|]; clear KF).
    clear OI TB.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof RSAW as SG. unfold rsa_alloc_wrap_stmtA, A_RSA_ALLOC_WRAP in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG with (h := h) (LB := LB) (LF := LF) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia; try eassumption; try reflexivity; try qlia.
      all: try (unfold RSA_ALLOC_WRAP_PHI, AVOL_CALL in *; clear - BUD; lia).
      all: try (rewrite unsigned_lit by (clear - SH SB64 SBLO HTOP TOP64; lia); apply uwc_data; [clear; lia| clear - SH SBLO; lia]).
      all: match goal with |- ?g => idtac "WRAP-PRE-LEFT:" g end. }
    clear SG.
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    unfold pk_alloc_wrap_postA in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    match type of HT2 with htop _ _ _ ?hh = _ => rename hh into h2 end.
    presA_transport HP2.
    assert (HPX : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(PKA, PKA + 16)] m m2).
    { eapply presA_trans.
      - eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) m); [exact (proj1 HH0)| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 (hcs asegs R HIA h) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact (proj1 HH0)| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (PKA + 16 - PKA) with 16 by lia; eapply aobj_crange; exact OBJ|]. apply Forall_nil.
      - eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SLO NEED0 NEEDA; lia| clear - LOS SLO NEED0 NEEDA; lia| clear; lia| intros y _; exact I]. }
    assert (WMX : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU WM HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in OBJ.
    clear CSOK SB64 SCS0 SCS HTOP. rewrite <- HT2 in TOP, CW.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_stack asegs R HIA h2) as SCS0.
    destruct CASES as [[E0 HH2] | (HN16 & HFR & HNS & HH2 & HNEW)].
    - (* [comment removed for export] *)
      match type of E0 with ?v = 0 => subst v end.
      pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      pose proof (munch_refl [(lo, bv_unsigned sp); (PKA, PKA + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      release_frame FR ST2 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_setup_postA.
      deexists 14. dexists m9, mo9, h2, (-0x3f80), 0, 0.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split.
      { eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_drop_below asegs R HIA h2 LB LF _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (PKA + 16 - PKA) with 16 by lia; eapply aobj_crange; exact OBJ|]. apply Forall_nil. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold PK_SETUP_PHI, ECKEY_ALLOC_WRAP_PHI, RSA_ALLOC_WRAP_PHI in *; clear - HV2; lia|]. split; [exact HFR2|].
      left. split; [reflexivity|]. split; assumption.
    - (* [comment removed for export] *)
      lazymatch type of HH2 with HM _ _ _ _ ((?c, _) :: _) _ _ => rename c into C end.
      pose proof (hm_top asegs R HIA h2 ((C, 232) :: LB) LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      dpose HFR as (HN0 & HNC & HND & HNAP).
      assert (APC : C + 232 <= PKA \/ PKA + 16 <= C).
      { eapply (fresh_apart_client R LB LF lo PKA 16 C 232 HFR); [| clear; lia| clear; lia| clear - ALO LOS; lia].
        eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (APS : C + 232 <= lo \/ bv_unsigned sp <= C) by (clear - HNC ALO LOS; lia).
      apply (client_wrange_mono L _ (((C, 232) :: LB) ++ fdata LF)) in CW; [| intros b Hb; right; exact Hb].
      pose proof (conj MI2 I) as MI2box. pose proof (conj HNEW I) as NEWbox. clear HNEW.
      pose proof (munch_refl [(lo, bv_unsigned sp); (PKA, PKA + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KC; zify_cond KC. { exfalso. rewrite ?unsigned_lit in KC by (clear - HN0 HNC; pose proof (alloc_ceiling_val R); lia). clear - KC HN0. lia. }
      clear KC.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      match goal with H : stk _ m9 lo _ |- _ => rename H into ST9 end.
      release_frame FR ST9 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_setup_postA.
      deexists 14. dexists m9, mo9, h2, 0, C, 232.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split.
      { eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_weaken asegs R ((C, 232) :: LB) LB LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2)
                  [(PKA, PKA + 16)]);
          [| intros b Hb; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below asegs R HIA h2 ((C, 232) :: LB) LF _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R ((C, 232) :: LB) LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (PKA + 16 - PKA) with 16 by lia; eapply aobj_crange; exact OBJ|]. apply Forall_nil. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold PK_SETUP_PHI, ECKEY_ALLOC_WRAP_PHI, RSA_ALLOC_WRAP_PHI in *; clear - HV2; lia|]. split; [exact HFR2|].
      right. split; [reflexivity|]. split; [exact HN16|]. split; [exact HFR|]. split; [exact HNS|]. split; [assumption|].
      split; [assumption|].
      split; [intros _; split; [reflexivity|]| intros NE; exfalso; apply NE; exact EINF].
      eapply rsa_at_munch; [exact (proj1 NEWbox)| exact MU| exact WM| exact (proj1 MI2box)| assumption| cbn [disjoint_from]; clear - APC APS; lia|].
      intros dd Hd HO. exfalso. unfold rsa_mpds, rsa_fresh, rsa_zero_mpds in Hd. cbn [In r_N r_E map] in Hd.
      destruct Hd as [<-|[<-|Hd]]; [cbn in HO; discriminate| cbn in HO; discriminate|].
      apply in_map_iff in Hd. ddestruct Hd as (o & <- & _). cbn in HO. discriminate.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03>0@D11189028015.96 D11189028015.97 D13564290403.141D2774095993.126 D35881667587.96 D35881667587.97 D45500527312.128D45500527312.140D50703400392.128D50703400392.140D50703400392.141D60109196847.128D60109196847.140D60109196847.141K3138337932.128 K3138337932.140 K3138337932.141 K64113782398.96 K64113782398.97 L11685632273.11 L11741095640.125L11741095640.133L11741095640.92 L1207681809.1   L12953351448.93 L13700332227.94 L14800215863.133L15756354262.4  L19354909044.93 L19935441546.124L19947928356.127L19947928356.139L25382082548.93 L26892418956.1  L26924648792.125L26924648792.133L26924648792.93 L27905070109.125L27905070109.137L28006807731.133L28901561692.2  L29010380273.133L29010380273.93 L29428324939.5  L29788790999.82 L31378308326.92 L31392867444.93 L3152797947.2   L35653441506.7  L35935759450.6  L36012194261.93 L37414286068.93 L38948636245.0  L39280637297.0  L39433892856.2  L40149296407.126L40281191306.3  L40834179097.95 L43059266230.90 L43300649301.0  L43442376564.92 L43654564952.125L43654564952.133L43654564952.93 L43909686289.7  L45073256784.5  L45825525979.10 L49628392745.6  L49952869148.92 L50560326147.1  L50984741682.93 L51229005915.124L51233362421.127L51233362421.139L51709126199.136L51709126206.124L53735823077.123L53735823077.131L547707976.3    L55360202074.7  L59308630630.3  L59308631400.3  L59308665200.3  L59499841752.125L59499841752.133L59499841752.93 L60098763854.3  L62018535662.1  L62022717421.7  L62037211595.8  L62383582187.16 L64116126217.2  L65499935772.81 L7510805464.125 L7510805464.133 L7510805464.93  L8929554458.9   L9410944361.4   P25610814625.125P25610814625.126Q10883991967.124Q10883991967.136Q11109677506.95 Q11109761264.94 Q13562048355.140Q14791076917.96 Q14792959895.114Q15641194494.125Q15641194494.137Q15643324129.92 Q15893294284.125Q18028566964.138Q18363861502.125Q18363861502.137Q18365925601.93 Q18694146040.95 Q20414272036.128Q20414272036.140Q20414272036.141Q20414272036.96 Q20414272036.97 Q21798041355.95 Q25157988860.95 Q25513505925.95 Q25513505925.96 Q25604052563.93 Q25604052563.94 Q25662358575.95 Q26574002091.126Q26574002091.138Q26574002091.139Q28119216628.96 Q29312881484.138Q29312881484.94 Q31228709292.95 Q31255363106.138Q31255363106.94 Q31394594844.95 Q32653239550.125Q32653239550.137Q32655500769.93 Q33915929245.125Q33915929245.137Q33918256002.93 Q35014437530.95 Q35717497884.95 Q36171140397.95 Q37426957269.93 Q37429021386.137Q37821600610.95 Q37821600610.96 Q3830427394.93  Q3832294941.125 Q3832294941.137 Q38722865500.95 Q38807819226.96 Q39939554818.93 Q39941750557.125Q39941750557.137Q41638037421.124Q41638037421.136Q42024716493.93 Q42026781138.137Q43909868710.96 Q44648843873.93 Q44650777470.125Q44650777470.137Q44767788171.94 Q45502445776.127Q45502445776.139Q49241094109.95 Q49698585326.94 Q49698585326.95 Q50558264496.138Q50558264496.94 Q50558457234.93 Q50560717965.137Q50701449160.127Q50701449160.139Q50701449160.140Q51233928830.125Q51233928830.137Q51235796833.93 Q53440817419.125Q53440817419.137Q53440894644.124Q53440894644.136Q53969758199.95 Q54520642575.125Q54520642575.137Q57744452505.94 Q63116570093.125Q63116570093.137Q6416456232.95  Q64255486968.95 Q64696564221.126Q65537657969.125Q65537657969.137Q65614050195.95 Q66522067074.93 Q66524131741.125Q66524131741.137Q807981431.96   Q9841302685.125 Q9841302685.137 Q9843367298.92  00001902K02m03>03m04e05E05g06G06i07K08408_09J0:=0;20;j0<`0=_0>K0>\0>o0?@0?E0?[0?l0@?0@M0@^0A20AF0A\0Am0B10BB0BU0Bf0CY0DR0EW0Eb0F50FF0FX0Fd0G50GF0GG0Gb0H70HM0H^0H_0H`0Hi0I:0IC0IV0JI0JJ0J[0Jl0K?0KP0KQ0Ka0L80L<0LV0L[0Ll0M=0MN0Ma0N40NE0N_0O;0OE0O\0Of0P20P@0PQ0Pd0Q50Q?0QB0QE0Qf0R`0Ra0Rm0S>0SQ0Sb0TG0TV0Th0U:0UC0UL0UZ0Uh0VE0W80Wk0X:0XI0XX0Y=0YM0Y\0Yk0Z:0ZJ0Zh0[H0[k0\^0]Z0][0]k0^L0_60_E0_T0_U0_l0`C0`Z0a20aZ0b<0bM0bV0b_0bh0c70cF0cU0d60dW0e80eI0eJ0eK0eT0e]0fP0gL0gm0hN0ho0i=0iR0j30jT0k50k>0kG0kP0kY0kZ0ki0l80lG0lU0lm0mG0mH0ma0n:0nC0nL0nU0n^0o60oP0om10<10K10Z10c10l11511>11O11X11a11o12Q13913I13J13K13[13k14O15015Q16217717X18918ZS1R5NEED05NEEDA2ra2sp3PKA4info2lo3POS3LOS3SLO3SPR3PKB4INFB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA4info2lo3POS3LOS3SLO3SPR3PKB4INFB2HB5Ha_st5Hl_st2s12s22s3S2sp3PKA4info1C3PKB2HB5Ha_st5Hl_stS2sp3PKA4info3PKBS1R3HIA1h2ra2sp3PKA4info3TOP3PKB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s03PKA4info3TOP3PKB2HB5Ha_st5Hl_st2s12s22s3S2sp3PKA4info3PKB2HB5Ha_st5Hl_stS2sp3PKA4info1C3PKB2HB5Ha_st5Hl_stS2sp3PKA4info3PKB2HB5Ha_st5Hl_stS2sp3PKA4info1C3PKB2HB5Ha_st5Hl_stS2sp3PKA4info1C3PKB2HB5Ha_st5Hl_stS1R2sp3PKA4info2lo3LOS3PKB2HB5Ha_st5Hl_stS1R2sp3PKA4info2lo1C3LOS3PKB2HB5Ha_st5Hl_stS1R2sp3PKA4info2lo1C3LOS3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA2lo2SX3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA2lo2SX1C3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA4info2lo2SX3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2ra2sp3PKA2lo2SX3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA2lo2SX3SLO3PKB2HB5Ha_st5Hl_st2s12s22s3S1R3HIA5NEED05NEEDA1h2sp2lo3LOS3SLO3TOP4HTOPS2sp3PKA4info3PKBS2sp3PKA4info1C3PKBS2sp3PKA4info3PKBS3PKAS2sp3PKA4info3PKB4INFBS2sp3PKA4info3PKBS2sp3PKA4info1C3PKBS1R2lo3LOS3ALOS2sp3PKA4info3PKBS2sp3PKA4info2lo3PKBS2sp3PKA4info2lo3PKBS2sp3PKA4info2lo1C3PKBS2sp3PKA4info3PKBS2spS2sp3PKA4info3PKBS2sp3PKA4info1C3PKBS2sp3PKA4info3PKBS1R5NEED05NEEDA2sp3PKA4info2lo3POS3SLO3SPR3PKB4INFBS1R5NEED05NEEDA2sp3PKA4info2lo3POS1C3SLO3SPR3PKB4INFB3HN0S1R5NEED05NEEDA2sp3PKA4info2lo3POS1C3LOS3SLO3ALO3SPR3PKB4INFB3HN03HNCS4info4INFBS2sp3PKA4info1C3PKBS2sp3PKA4info3PKBS1R2lo3LOS3ALO3ACPS2sp3PKA3PKBS2sp3PKA4info3PKBS2sp3PKA4info3PKBFS1R3HIA1h2sp2lo3TOP4HTOP2h2S2sp3PKA2lo1C3APC3APSS2sp3PKA4info3PKB4INFBS2sp3PKA4info3PKBSSS4info2EIS2sp3PKA4info3PKBS1R3HIA1hS1R2sp3PKA4info3PKBS1R5NEED05NEEDA2sp3PKA4info2lo3POS3SLO3SPR3PKB4INFBSS2sp3PKA4info3PKBS2sp3PKA4info3PKBS2sp3PKA4info1C3PKBS2sp3PKA4info3PKBFS1R3HIA1h2h23HV2S3PKA3POS4PK471q1r1H2H0S2spS2sp3PKA4info3POS3PKB4PK47S3PKAS2sp3PKA4info3PKBS2sp3PKA4info3PKBS2sp3PKA4info3PKBS2sp3PKA4info1C3PKBS2sp3PKA4info1C3PKBS2sp3PKA4info3PKBS2sp3PKA4info3POS3PKB4PK47S2sp3PKA4info3POS1C3PKB4PK47S1R3HIA2h2S1R2sp2lo3LOS3ALO1C3HNCS1C3HN02KCS4info2IB2KIS4info4INFB2EQS2sp3PKA4info3PKBS2sp3PKA4info1C3PKBS2sp3PKA4info3PKBS1R2lo3LOSS1RS1RS1R5NEED05NEEDA2sp2lo3LOS3SLO3SPRS1R3HIA5NEED05NEEDA1h2sp3PKA2lo3LOS3SLO3TOP4HTOP4SBLO2Q21QFS2sp3PKA3PKBS2sp3PKA4info3PKBS2sp3PKA4info1C3PKBS2sp3PKA4info3PKBS1R3HIA1h3PKA4SB644HTOP4SBLO5TOP642SHS1R3PKA4SBLO2SHS2sp3PKA2lo2SX3PKBS2sp3PKA2lo2SX3PKBS3PKA3PKBS3PKA3PKBS3PKA4info3PKBS3PKA4info3PKBS3PKA4info3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp3PKA2lo3LOS3SLO4SB643SPR4SBLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3LOS3SLO4SB643SPR4SBLO3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS1R5NEED05NEEDA2sp3PKA2lo3LOS3SLO3PKBS3PKA3POS3PKB2HBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS1R3PKA4IMG'3PKBS2sp3PKA2lo3PKB2HB5Ha_st5Hl_stS2sp3PKA2lo1C3PKB2HB5Ha_st5Hl_stS2sp3PKA4info2lo3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2ra2sp3PKA2lo3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA2lo3SLO3PKB2HB5Ha_st5Hl_st2s12s22s3FS1R3PKA4IMG'3PKBS2ra2sp3PKA2lo3PKB2HB5Ha_st5Hl_stS2sp2s03PKA2lo3PKB2HB5Ha_st5Hl_st2s12s22s3S2sp3PKA3PKB2HBS2sp3PKA3PKB2HBFS3PKA3PKB4PK472HB5Ha_stS3PKA3PKB4PK472HB5Ha_stS3PKA3PKB4PK472HB5Ha_stS1R3HIA1h2sp3PKA3TOP3PKBS2sp3PKA4info3AL83POS1C3SPR3PKB4INFB3HN0S2sp3PKA4info3AL83POS3SPR3PKB4INFBS1R3PKA5ALWF'3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R3PKA5ALWF'3PKBFFS3PKA3PKBS3PKA3PKBS1R5NEED05NEEDA2ra2sp3PKA2lo3SLO3PKB2HB5Ha_st5Hl_stS1R5NEED05NEEDA2sp2s03PKA2lo3SLO3PKB2HB5Ha_st5Hl_st2s12s22s3S1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS3PKA4info3PKBS1R2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBFS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS3PKA4info3PKBS3PKA3PKB2HB5Ha_st5Hl_stS3PKA1C3PKB2HB5Ha_st5Hl_stFS2sp3PKA3SPR3PKB2HB5Ha_stS2sp3PKA3SPR3PKB2HB5Ha_stS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKB2HB5Ha_st5Hl_stS3PKA1C3PKB2HB5Ha_st5Hl_stS3PKA4info3PKB2HB5Ha_st5Hl_stS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS2sp3PKA2lo3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS3PKA3PKBS1R3PKA5ALWF'3PKBS3PKA3PKBS3PKA3PKBS3PKA4info3PKBS2sp3PKA4info3AL83POS3SPR3PKB4INFBS2sp3PKA4info3AL83POS1C3SPR3PKB4INFB3HN0S1R3PKA4IMG'3PKBFFS3PKA3POS3PKB2HBS3PKA3POS3PKB2HBS2sp3PKA4info3POS3SPR3PKB4INFB5INFALS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA4info2lo3POS3LOS3SLO3SPA4SB643SPR4SBLO3PKB4INFBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKBS1R5NEED05NEEDA2sp3PKA2lo3SLO3PKB". (* [comment removed for export] *)
  #[using="IMG RTC ECW NEED0 NEEDA"] Lemma A_pk_setup_ec : ltac2:(CDefT.buildp (gd_tbl_A_pk_setup ()) "Ph,(5.$45.VR,VHIA,)PLB,(32.$33.)PLF,(32.$33.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(34.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPKA,$6.Pinfo,$6.Plo,$6.P,(27.$45.VR,VHIA,R29.R28.R27.R5.)P,(1?.$45.VR,VHIA,R2:.R5.)P,(28.$45.R7.R5.(18.$29.(2:.(<.&40.=))(18.$29.(2:.(<.&40.=))(1<.$29.))))P,(8.$6.(2;.R6.+8.)=)P,(35.=R7.)P,(36.$6.R7.$48.)P,(26.(21.(1;.R9.+10.)R7.)(21.(12.&40.R2;.)R9.))P,(37.$45.(38.VR,)(20.$45.VR,VHIA,R30.)R<.R:.+10.)P,(39.(3:.VR,)(3;.$33.R30.(3<.R2?.))R9.(1=.$45.VR,VHIA,R31.)R;.+10.)P,(11.$45.R>.R:.(12.&40.R2>.))P,(21.(16.VR,)R;.)P,(21.R<.(3=.(3=.(3=.(12.&40.R30.)+80.)(3>.VR,))(3?.VR,)))P,(21.(12.&40.R31.)(1=.$45.VR,VHIA,R35.))P,(8.$6.(2;.(12.&40.R32.)+10.)=)P,(10.$45.R13.)P,(8.(2.&40.)R32.(<.&40.(40.VR,)))P,(21.(1;.(22.$45.VR,VHIA,R39.)$23.)$41.)P,(21.(1;.(24.$45.VR,VHIA,R3:.)(25.=))$42.)P,(8.(2.&40.)R2?.(<.&40.R15.))P,(8.(2.&40.)R2?.(<.&40.R15.))(43.$45.(44.$45.VR,VHIA,VMT,$46.R3=.R3<.R3;.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R19.R18.)(9.(:.(;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(<.&40.$47.)R1:.(>.(2.&40.))R19.(?.$45.))R18.))")
(* [comment removed for export] *).
  Proof.
    unfold A_PK_SETUP. intros until lo.
    intros HH HKmo HPK AL8 POS EI SX OBJ CW ST LOS SLO TOP SPA MI TPV BUD BUDF -> ->.
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
    pose proof (art_stk_high asegs R HIA) as SBLO.
    pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SLO SPR NEED0 NEEDA; lia)) as TOP64.
    pose proof (rw_cells_bound _ _ _ _ HPK) as PKB. cbn [cells_size csize Nat.add] in PKB.
    assert (PK47 : PKA + 16 <= 2^47).
    { destruct (hcs_app asegs R HIA h PKA 16 (aobj_crange _ _ _ _ _ _ OBJ) ltac:(lia)) as [[_ Q]|[_ Q]]; [| exact Q].
      destruct (hcs_app asegs R HIA h _ _ SCS0 ltac:(clear - HTOP TOP SLO LOS NEED0 NEEDA; lia)) as [[_ Q2]|[_ Q2]];
        clear - Q Q2 SB64 SBLO HTOP TOP SLO LOS NEED0 NEEDA; lia. }
    assert (SH : 0 <= Z.shiftr PKA 3 < 2^44) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - POS PK47; Z.div_mod_to_equations; lia).
    assert (INFB : 991744 <= info <= 992000).
    { clear - EI. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. lia. }
    assert (INFAL : info mod 64 = 0).
    { clear - EI. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. destruct EI as [<-|[<-|[<-|[]]]]; reflexivity. }
    assert (IB : 0 < info < 2^32) by (clear - INFB; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp); (PKA, PKA + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold PK_SETUP_PHI, ECKEY_ALLOC_WRAP_PHI in BUD.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KI; zify_cond KI; [exfalso; clear - KI IB; rewrite ?unsigned_lit in KI by lia; lia|]. clear KI.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HHx : HM _ _ _ h _ LF mx |- _ =>
        pose proof (abase_got _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GOT; pose proof (abase_gsb _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GSB; rewrite (proj1 IMG') in GOT end end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    lazymatch goal with HHx : HM _ _ _ h _ LF m1 |- _ => rename HHx into HH1 end.
    assert (OI : aobj asegs AL (hcs asegs R HIA h) m1 (info + 72) 8).
    { pose proof (hm_img_shadow asegs R HIA h _ LF m1 HH1) as ISH. pose proof (hcs_img_cs R HIA h IMG (proj2 (proj2 (proj2 IMG')))) as ICS.
      clear - EI ISH ICS. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI.
      destruct EI as [<-|[<-|[<-|[]]]]; (eapply aobj_img; [exact ICS| exact ISH| vm_compute; reflexivity]). }
    assert (TB : ro_cells asegs m1 (info + 72) [CB 8 [Z_to_bv 8 184; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
    { pose proof (RTC m1 (hm_rtc asegs R HIA h _ LF m1 HH1)) as RT.
      clear - EI RT. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI.
      destruct EI as [<-|[<-|[<-|[]]]];
        [ exact (asan_rtc_const m1 (991744 + 72) [Z_to_bv 8 184; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] RT ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
        | exact (asan_rtc_const m1 (991872 + 72) [Z_to_bv 8 184; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] RT ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
        | exact (asan_rtc_const m1 (992000 + 72) [Z_to_bv 8 184; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] RT ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) ]. }
    clear EI.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. try (if_cases KF; zify_cond KF; [exfalso; revert KF; clear; intros KF; rewrite ?unsigned_lit in KF by lia; cbn in KF; lia|]; clear KF).
    clear OI TB.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof ECW as SG. unfold eckey_alloc_wrap_stmtA, A_ECKEY_ALLOC_WRAP in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG with (h := h) (LB := LB) (LF := LF) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia; try eassumption; try reflexivity; try qlia.
      all: try (unfold ECKEY_ALLOC_WRAP_PHI, AVOL_CALL in *; clear - BUD; lia).
      all: try (rewrite unsigned_lit by (clear - SH SB64 SBLO HTOP TOP64; lia); apply uwc_data; [clear; lia| clear - SH SBLO; lia]).
      all: match goal with |- ?g => idtac "WRAP-PRE-LEFT:" g end. }
    clear SG.
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    unfold pk_alloc_wrap_postA in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    match type of HT2 with htop _ _ _ ?hh = _ => rename hh into h2 end.
    presA_transport HP2.
    assert (HPX : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(PKA, PKA + 16)] m m2).
    { eapply presA_trans.
      - eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) m); [exact (proj1 HH0)| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 (hcs asegs R HIA h) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact (proj1 HH0)| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (PKA + 16 - PKA) with 16 by lia; eapply aobj_crange; exact OBJ|]. apply Forall_nil.
      - eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SLO NEED0 NEEDA; lia| clear - LOS SLO NEED0 NEEDA; lia| clear; lia| intros y _; exact I]. }
    assert (WMX : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU WM HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in OBJ.
    clear CSOK SB64 SCS0 SCS HTOP. rewrite <- HT2 in TOP, CW.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_stack asegs R HIA h2) as SCS0.
    destruct CASES as [[E0 HH2] | (HN16 & HFR & HNS & HH2 & HNEW)].
    - (* [comment removed for export] *)
      match type of E0 with ?v = 0 => subst v end.
      pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      pose proof (munch_refl [(lo, bv_unsigned sp); (PKA, PKA + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      release_frame FR ST2 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_setup_postA.
      deexists 14. dexists m9, mo9, h2, (-0x3f80), 0, 0.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split.
      { eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_drop_below asegs R HIA h2 LB LF _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (PKA + 16 - PKA) with 16 by lia; eapply aobj_crange; exact OBJ|]. apply Forall_nil. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold PK_SETUP_PHI, ECKEY_ALLOC_WRAP_PHI, RSA_ALLOC_WRAP_PHI in *; clear - HV2; lia|]. split; [exact HFR2|].
      left. split; [reflexivity|]. split; assumption.
    - (* [comment removed for export] *)
      lazymatch type of HH2 with HM _ _ _ _ ((?c, _) :: _) _ _ => rename c into C end.
      pose proof (hm_top asegs R HIA h2 ((C, 256) :: LB) LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      dpose HFR as (HN0 & HNC & HND & HNAP).
      assert (APC : C + 256 <= PKA \/ PKA + 16 <= C).
      { eapply (fresh_apart_client R LB LF lo PKA 16 C 256 HFR); [| clear; lia| clear; lia| clear - ALO LOS; lia].
        eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (APS : C + 256 <= lo \/ bv_unsigned sp <= C) by (clear - HNC ALO LOS; lia).
      apply (client_wrange_mono L _ (((C, 256) :: LB) ++ fdata LF)) in CW; [| intros b Hb; right; exact Hb].
      pose proof (conj MI2 I) as MI2box. pose proof (conj HNEW I) as NEWbox. clear HNEW.
      pose proof (munch_refl [(lo, bv_unsigned sp); (PKA, PKA + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KC; zify_cond KC. { exfalso. rewrite ?unsigned_lit in KC by (clear - HN0 HNC; pose proof (alloc_ceiling_val R); lia). clear - KC HN0. lia. }
      clear KC.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      match goal with H : stk _ m9 lo _ |- _ => rename H into ST9 end.
      release_frame FR ST9 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_setup_postA.
      deexists 14. dexists m9, mo9, h2, 0, C, 256.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [exact WMX|].
      split.
      { eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_weaken asegs R ((C, 256) :: LB) LB LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2)
                  [(PKA, PKA + 16)]);
          [| intros b Hb; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below asegs R HIA h2 ((C, 256) :: LB) LF _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R ((C, 256) :: LB) LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
          [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | exact MU | exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (PKA + 16 - PKA) with 16 by lia; eapply aobj_crange; exact OBJ|]. apply Forall_nil. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|]. split; [unfold PK_SETUP_PHI, ECKEY_ALLOC_WRAP_PHI, RSA_ALLOC_WRAP_PHI in *; clear - HV2; lia|]. split; [exact HFR2|].
      right. split; [reflexivity|]. split; [exact HN16|]. split; [exact HFR|]. split; [exact HNS|]. split; [assumption|].
      split; [assumption|].
      split; [intros EQ; exfalso; clear - EQ INFB; unfold A_RSA_INFO in EQ; lia| intros _; split; [reflexivity|]].
      ddestruct (proj1 NEWbox) as (idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & pd & qX & qY & qZ & KP).
      dexists idpad, pP, pA, pB, pX, pY, pZ, pN, hpad, pd, qX, qY, qZ.
      eapply ecp_keypair_at_munch; [exact KP| exact MU| exact WM| exact (proj1 MI2box)| assumption| cbn [disjoint_from]; clear - APC APS; lia|].
      intros dd Hd HO. exfalso. clear - Hd HO. unfold kp_mpds, kp_init, grp_mpds, grp_init, pt_mpds, pt_init in Hd. cbn in Hd.
      repeat (destruct Hd as [<-|Hd]; [cbn in HO; discriminate|]). destruct Hd.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_pk_setup_spec : ltac2:(CDefT.buildp (gd_tbl_A_pk_setup ()) "PR,$49.PHIA,(4:.$45.R1.)PMT,(32.$4;.)P,(4<.(38.R3.))P,Pm,P,(2.&40.)(3.(2.&8.))P,(4=.R5.R1.)(4>.R2.)P,(8.$6.(4?.R5.)+69484.)P,(8.$6.(50.R6.)$51.)P,(21.=(3>.R7.))P,(21.=(3?.R8.))(52.$45.R9.R8.R7.$46.$48.$47.)")
(* [comment removed for export] *).
Proof.
  intros R HIA MT IMG RTC CAL AMS N0 NA. unfold pk_setup_stmtA. intros until lo.
  intros HH HK HPK AL8 POS [EI|EI] SX OBJ CW ST LOS SLO TOP SPA MI TPV BUD BUDF E0 E1.
  - eapply (A_pk_setup_rsa R HIA MT IMG RTC (A_rsa_alloc_wrap_spec R HIA IMG CAL AMS N0 NA) N0 NA); eassumption.
  - eapply (A_pk_setup_ec R HIA MT IMG RTC (A_eckey_alloc_wrap_spec R HIA MT IMG CAL AMS N0 NA) N0 NA); eassumption.
Qed.

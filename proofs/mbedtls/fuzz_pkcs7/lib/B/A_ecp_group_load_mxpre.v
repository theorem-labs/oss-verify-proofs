(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_copy A_mpi_bitlen A_ecp_defs A_ecp_statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_ecp_group_load.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_ecp_group_load_mxpre () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.curve_addrs"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_P"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.cP"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_N"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.cN"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.mx_nbits"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_modp"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "gl_mx_ret"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.mx_a24"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "gl_mx_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load.gl_init_cells"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "gl_mx_pre_post"].


(* [comment removed for export] *)
Definition gl_mx_ret (id : Z) : Z := if id =? 9 then 0xd3134 else 0xd1530.
Definition gl_mx_cells (m : mem) (A id : Z) (idpad pP pA pB pX pY pZ pN hpad : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mxpre ()) "Zca,$0.(1.O:.)(2.(3.$4.O<.O;.(5.$6.(7.(8.&40.O:.))(5.$6.(7.O9.)(9.$6.))))(2.(3.$4.O<.(:.O;.+8.)(;.(<.R1.)(8.&40.+1.)(=.(>.(?.&40.)(10.O:.)))O8.))(2.(3.$4.O<.(:.O;.+18.)(;.=(8.&40.+1.)=O7.))(2.(3.$4.O<.(:.O;.+28.)(;.=(8.&40.+1.)=O6.))(2.(3.$4.O<.(:.O;.+38.)(;.=(8.&40.+1.)=O5.))(2.(3.$4.O<.(:.O;.+48.)(;.=(8.&40.+1.)=O4.))(2.(3.$4.O<.(:.O;.+58.)(;.=(8.&40.+1.)=O3.))(2.(3.$4.O<.(:.O;.+68.)(;.(11.R1.)(8.&40.+1.)(=.(>.(?.&40.)(12.O:.)))O2.))(3.$4.O<.(:.O;.+78.)(5.$6.(13.(8.&40.(14.(10.O:.)(=.(>.(?.&40.)(10.O:.))))))(5.$6.(13.(8.&40.(15.O:.)))(5.$6.(7.(8.&40.+2.))(5.$6.(7.O1.)(5.$6.(13.(8.&40.(16.R1.)))(5.$6.(13.(8.&40.=))(5.$6.(13.(8.&40.=))(5.$6.(13.(8.&40.=))(5.$6.(13.(8.&40.=))(5.$6.(13.(8.&40.=))(9.$6.))))))))))))))))))))")
(* [comment removed for export] *).

Definition gl_mx_pre_post (R : art_layout) (HIA : artA asegs R) (h : HST asegs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A id : Z) (idpad pP pA pB pX pY pZ pN hpad : word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mxpre ()) "Lms',$17.(18.(?.&40.)Lt0,(?.&40.)(18.(?.&40.)Lt1,(?.&40.)(18.(?.&40.)Lt2,(?.&40.)(18.(?.&40.)La2,(?.&40.)(18.(?.&40.)La3,(?.&40.)(18.(?.&40.)La4,(?.&40.)(18.(?.&40.)La5,(?.&40.)(18.(?.&40.)La6,(?.&40.)(18.(?.&40.)La7,(?.&40.)(18.(?.&40.)Lt3,(?.&40.)(18.(?.&40.)Lt4,(?.&40.)(18.(?.&40.)Lt5,(?.&40.)(18.(?.&40.)Lt6,(?.&40.)(18.P,(?.&40.)(19.(?.&8.))Lm',P,(?.&40.)(19.(?.&8.))(2.(1:.$17.R?.(1;.(1<.(8.&40.(1=.O<.))(8.&40.(:.(1>.&40.O1>.)-20.))O1=.O1<.R>.R=.R<.(8.&40.O=.)(8.&40.O<.)(8.&40.(:.O=.+18.))(8.&40.(1?.O<.))R;.R:.R9.R8.R7.R6.(8.&40.(20.(21.O24.)))O18.O17.O16.O15.O14.O13.O12.O11.O10.R5.R4.R3.R2.)O?.(8.&40.$22.)O>.(23.(?.&40.))R1.(24.$4.)))(2.(25.(5.(26.$27.$27.)(28.$27.$27.O=.(:.O=.+<0.))(5.(26.$27.$27.)(28.$27.$27.O2.(1>.&40.O1>.))(9.(26.$27.$27.))))O1.R1.)(2.(29.$4.O1.R1.)(2.(2:.$4.R1.)(2.(2;.R1.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.)(2.(3.$4.R1.(:.(1>.&40.O1>.)-20.)(5.$6.(13.O19.)(5.$6.(13.O1:.)(5.$6.(13.O1;.)(5.$6.(13.O1?.)(9.$6.))))))(2.(2<.$4.R1.O2.(:.(1>.&40.O1>.)-20.))(2=.$4.O24.O23.O22.O21.O20.R1.))))))))))))))))))))))")
(* [comment removed for export] *).

Section GLC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03C0@C17025492443.118D17681063743.98 D19435425286.113D27817177663.113D27817177663.97 D27817177663.98 D29659146502.98 D37974266175.113D58799299509.113D58799299509.97 D58799299509.98 D60109446735.118D64311484648.118D9228611334.113 K11493750132.118K15064807540.118K33231037556.118K36787415924.118K40344297076.118K446595215.113  K446595215.97   K446595215.98   K50584482736.118K54933706612.118K58490083956.118K62048029044.118L11014368388.13 L11016396417.6  L11016802336.6  L11506788113.3  L11671740496.94 L12696972339.2  L12803751780.92 L13584346876.94 L13885609679.109L14601520535.2  L15051368977.3  L18223745967.109L20780617598.108L22168541005.6  L24617487510.2  L25019740159.1  L25964569660.3  L28576112895.1  L28902963962.93 L2920766268.1   L29428324939.5  L2952520574.93  L29790966853.2  L30875333039.109L31056777086.93 L31158092880.109L32134534655.1  L32510975280.109L3304963839.1   L33226651153.3  L3432542248.1   L34730255137.0  L35653441506.7  L35744910738.0  L36783814929.3  L3686674472.1   L37179380432.94 L38235734261.1  L39217970607.94 L40340425745.3  L41528389327.94 L43207602000.93 L43884818473.2  L440278008.2    L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L46566552559.108L46742854911.1  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L49919594191.109L50299228671.1  L50597913045.3  L52843527472.94 L53857698559.1  L54662891932.109L54937175313.3  L54968017161.1  L56282437220.108L58098026908.94 L58494339089.3  L59220218468.108L59577639290.93 L60058665040.109L60098763854.3  L60897450748.109L62052031249.3  L62893530908.94 L62905296796.109L66151427842.16 L67360804024.1  L67399942378.14 L6861337599.1   L7193111478.5   L8073947620.108 L858388636.93   N21806751459.119N37104593031.119O17025492443.118O21061669077.118O21610544085.118O26328763605.118O28312938197.118O30724803029.118O31711449813.118O34798215125.118O37051008023.118O40145708501.118Q10680085182.109Q10680111115.110Q11555852190.93 Q1739419909.110 Q17664808108.109Q17683010879.97 Q19433505798.112Q21710694325.93 Q21712770443.94 Q21891839631.110Q22455687044.94 Q22718020363.110Q22718432309.109Q23016664812.110Q23016664812.95 Q24878157199.95 Q25272442639.110Q25855820340.110Q26933099022.110Q26933099022.95 Q27819423807.112Q27819423807.96 Q27819423807.97 Q27987727582.110Q27987727582.94 Q27987727582.95 Q29661094662.97 Q33462842895.110Q33761161355.110Q33761316789.109Q34249054829.110Q36804895414.109Q37972319039.112Q38151108574.110Q38248387216.118Q39733111860.95 Q39772081419.95 Q39772454703.94 Q39935065476.118Q40344550046.113Q40344550046.97 Q40344550046.98 Q40509833325.95 Q42558789799.109Q43567556498.94 Q43879899724.118Q44416233743.95 Q45506725451.94 Q45930014174.95 Q46358708205.110Q4658344367.109 Q4658693003.110 Q47412156653.110Q48867244141.94 Q48965536812.109Q49303179183.94 Q49303289227.95 Q49698585326.111Q49698585326.95 Q49698585326.96 Q49733646878.109Q49919631725.110Q50295957676.93 Q50656923446.94 Q52666267919.95 Q52773753861.95 Q53092503701.109Q53677133549.95 Q569528972.109  Q58797117877.112Q58797117877.96 Q58797117877.97 Q58833082637.110Q60260471301.110Q62025615085.95 Q63417588480.94 Q63589373316.109Q64525772082.94 Q65109593869.95 Q65371908960.94 Q65903965583.94 Q66760123006.109Q66908508420.94 Q67366860043.95 Q67367208235.94 Q67977388214.94 Q68302160783.110Q7192832789.98  Q8182593438.109 Q856114005.109  Q9230853382.112 00000100M00l01H01d02@02\03803W04304O04d05?05[05j06906H06W06f07L07o08R08a09009?09N09O09P09Q09R09^09_09o0:;0:G0:N0:O0:[0:k0;;0;B0;E0;P0;S0;c0;f0<80<H0<I0<U0<e0=10=40=@0=C0=D0=G0=H0=`0=a0=b0=e0>10>50>A0>B0>N0>Z0>a0>b0>c0>d0>e0>f0>g0>h0?80?;0?<0?H0?I0?J0?V0?Y0?Z0?f0?i0@50@60@90@I0@U0@V0@f0A60AB0AL0AX0AY0Ae0B10BQ0BT0BU0BX0Bk0C;0CG0CY0Ck0D60D70D80D90D:0D;0D<0D=0D>0D?0DE0DK0DQ0D_0De0E;0ET0EZ0E`0Ef0El0F20F80F>0FD0FJ0FP0FV0Fn0GF0G\0H20HH0HV0Hd0I20IH0IN0IT0IZ0J20J80JN0J\0Je0Jk0K10K70KG0Kf0LB0L^0M60M<0MB0MN0MT0MZ0Mh0N@0NF0NL0Nd0O<0OB0OH0ON0O^0On0P>0PD0P\0Pb0Ph0Pn0Q<0QB0QZ0Q`0R90RO0Re0Rf0S40SL0SR0SX0S^0S_0Se0Sk0T10T70T=0TC0TI0TO0U10U70U=0USFS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2pP2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2pP2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS1R2ra2sp1A2lo3LOS2TBS1R3HIA1h2ra2sp1A2lo3TOP2TBS2ra2sp1A2TB3HB05Ha_st5Hl_stS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2pP3SLO2DS2TB3HB05Ha_st5Hl_stS2sp1A2lo3SLO2DS2TB3HB05Ha_st5Hl_stS2sp1A2lo3SLO2DS2TB3HB05Ha_st5Hl_stS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBFFFFS2ra2sp1A2TBFS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS1A3POSFS2ra2sp1A2TBS2ra2sp1A3POS2TBS1R2lo3LOS3ALO1HS2sp2loS1AS2sp2lo3SLOS1AS2ra2sp1A3POS2TBS1AS1R2lo3LOS3ALO3ACPS2ra2sp1A3POS2TBFS2ra2sp1A2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS1AS2ra2sp1A2TBS1AFS1ASS1R3HIA1h2sp2lo3TOP4HTOPSFS1AS2ra2sp1A2TBS2loS2ra2sp1A2TBFS2ra2sp1A2TBS2ra2sp1A2TBS2sp2loFFFFFFFS2ra2sp1A3POS2TBS1AFS2sp1A2lo2DSFFS2ra2sp1A2TBS1AFS2ra2sp1A2TBS1AS2ra2sp1A2TBFS1AS2ra2sp1A3POS2TBS2ra2sp1A2TBFS2ra2sp1A3POS2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS1R2lo3LOSS2ra2sp1A2TBFS2ra2sp1A2TBS2ra2sp1A2TBS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS1AS2sp2lo3SLO3SPR3LO0S2ra2sp1A3POS2TBS2ra2sp1A2TBS2sp1A2lo2TB3x151CS2sp1A2lo2TB3x151CS2sp2lo3SLOFFFFFFFFFS1A2TBS1A2TBS1A2TBS1A3POS2TB3HB0S1A2TBS1A2TB3HB05Ha_st5Hl_stS1A2pP2TB3HB05Ha_st5Hl_stS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS2ra2sp1A3AL83POS3SPR2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stS1A3POS2TB3HB0S1A3POS2TB3HB0S1A3POS2TB3HB0S1A2TB3HB05Ha_st5Hl_stS1A2TBS1A2TBS1A2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TB3HB05Ha_st5Hl_stS1A3POS2TB3HB0S1A2lo2TBS1A2TBS1A2TBS1A2TBS2sp1A2lo3SLO2TBS2sp1A2lo2pP2TB3HB05Ha_st5Hl_stS2sp1A2lo2TB3HB05Ha_st5Hl_stS2sp1A2lo2TB3HB05Ha_st5Hl_stS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS2sp1A2lo2TBS1A2TBS1A2TBS1A3POS2TB3HB0S2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS2ra2sp1A3AL83POS3SPR2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS1A2TBS1A2TB3HB05Ha_stS1A2TB3HB05Ha_stS1A2TB3HB05Ha_stS1A2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS1A2TBS1A3POS2TB3HB0S1A2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2pP2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stFS1A3POS2TB3HB0S2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS1A2TBFS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1R2sp1A2lo3LOS3SLO3ALO3ACP3SPR2TBS1A2TBS1A2TBS1A2TB3HB05Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG"] Lemma mxpre9 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mxpre ()) "Ph,(2>.$4.VR,VHIA,)PLB,(2?.$30.)PLF,(2?.$30.)Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pxa0,(?.&40.)Pxa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)Pxra,(?.&40.)PF,(31.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(19.(?.&8.))PA,$27.Plo,$27.Pidpad,(?.&40.)PpP,(?.&40.)PpA,(?.&40.)PpB,(?.&40.)PpX,(?.&40.)PpY,(?.&40.)PpZ,(?.&40.)PpN,(?.&40.)Phpad,(?.&40.)P,(2=.$4.VR,VHIA,R31.R30.R2?.R<.)P,(32.R=.R<.+9.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(1:.$27.(33.R=.+8.)=)P,(34.=R>.)P,(3.$4.R10.(:.(1>.&40.R31.)-20.)(5.$6.(13.R21.)(5.$6.(13.R2:.)(5.$6.(13.R2;.)(5.$6.(13.R32.)(9.$6.))))))P,(2<.$4.R11.R?.(:.(1>.&40.R32.)-20.))P,(35.(36.VR,)R10.)P,(35.R11.(37.(37.(1>.&40.R34.)+20.)+40.))P,(35.(1>.&40.R35.)(38.$4.VR,VHIA,R39.))P,(1:.$27.(33.(1>.&40.R36.)+10.)=)P,(39.(35.(:.R15.+<0.)R14.)(35.(1>.&40.R37.)R15.))P,(2:.$4.R17.)P,(3:.$4.(21.VR,)(3;.$4.VR,VHIA,R3=.)R18.R17.+<0.)P,(3<.(3=.VR,)(3>.$30.R3=.(3?.R3<.))(36.VR,)(38.$4.VR,VHIA,R3>.)R18.+<0.)P,(1:.$27.(33.(1>.&40.R3<.)+2.)=)(40.$4.(21.VR,)(3;.$4.VR,VHIA,R40.)(41.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+9.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(1;.(1<.R1>.(8.&40.(:.(1>.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(8.&40.R1:.)(8.&40.+9.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(8.&40.(20.(21.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(8.&40.+=2?>8.)R1<.(23.(?.&40.))R1;.(24.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. (intros HH dd_H; ddestruct dd_H as (HD & HP & HA & HB & HX & HY & HZ & HN & HT); intros AL8 POS FR ST LOS SLO TOP SPA DS MI OA CWA RAE).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (munch_refl [(A, A + 192); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (lock MI) as MI00.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (A_curve_statics m 9 MI ltac:(clear; lia)) as CS. dpose CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    do 39 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_P end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_P, MIc : mem_inv _ mq_P |- _ =>
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 9)) (cP 9) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 9)) (4 * Z.of_nat (length (cP 9))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 9)) (cP 9) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 9)); vm_compute (Z.of_nat (length (cP 9))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 39 zstep.
    finish; try eassumption; try (clear - SLO; lia).
    all: try (unfold gl_mx_cells; cbv zeta; do 8 (split; [assumption|]); assumption).
    all: match goal with |- ?g => idtac "MXPRE9-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03C0@C17025492443.118D17681063743.98 D19435425286.113D27817177663.113D27817177663.97 D27817177663.98 D29659146502.98 D37974266175.113D58799299509.113D58799299509.97 D58799299509.98 D60109446735.118D64311484648.118D9228611334.113 K11493750132.118K15064807540.118K33231037556.118K36787415924.118K40344297076.118K446595215.113  K446595215.97   K446595215.98   K50584482736.118K54933706612.118K58490083956.118K62048029044.118L11014368388.13 L11016396417.6  L11016802336.6  L11506788113.3  L11671740496.94 L12696972339.2  L12803751780.92 L13584346876.94 L13885609679.109L14601520535.2  L15051368977.3  L16100834090.14 L18223745967.109L20780617598.108L24617487510.2  L25019740159.1  L25964569660.3  L28576112895.1  L28902963962.93 L2920766268.1   L29428324939.5  L2952520574.93  L29790966853.2  L30875333039.109L31056777086.93 L31158092880.109L32134534655.1  L32510975280.109L3304963839.1   L33226651153.3  L3432542248.1   L34730255137.0  L35653441506.7  L36783814929.3  L3686674472.1   L37179380432.94 L38235734261.1  L39217970607.94 L40340425745.3  L41528389327.94 L43207602000.93 L43884818473.2  L440278008.2    L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L46566552559.108L46742854911.1  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L49919594191.109L50299228671.1  L50597913045.3  L52843527472.94 L53857698559.1  L5462346957.6   L54662891932.109L54937175313.3  L54968017161.1  L56282437220.108L57784374802.0  L58098026908.94 L58494339089.3  L59220218468.108L59577639290.93 L60058665040.109L60098763854.3  L60897450748.109L62052031249.3  L62893530908.94 L62905296796.109L66151427842.16 L67360804024.1  L6861337599.1   L7193111478.5   L8073947620.108 L858388636.93   N21806751459.119N37104593031.119O17025492443.118O21061669077.118O21610544085.118O26328763605.118O28312938197.118O30724803029.118O31711449813.118O34798215125.118O37051008023.118O40145708501.118Q10680085182.109Q10680111115.110Q11555852190.93 Q1739419909.110 Q17664808108.109Q17683010879.97 Q19433505798.112Q21710694325.93 Q21712770443.94 Q21891839631.110Q22455687044.94 Q22718020363.110Q22718432309.109Q23016664812.110Q23016664812.95 Q24878157199.95 Q25272442639.110Q25855820340.110Q26933099022.110Q26933099022.95 Q27819423807.112Q27819423807.96 Q27819423807.97 Q27987727582.110Q27987727582.94 Q27987727582.95 Q29661094662.97 Q33462842895.110Q33761161355.110Q33761316789.109Q34249054829.110Q36804895414.109Q37972319039.112Q38151108574.110Q38248387216.118Q39733111860.95 Q39772081419.95 Q39772454703.94 Q39935065476.118Q40344550046.113Q40344550046.97 Q40344550046.98 Q40509833325.95 Q42558789799.109Q43567556498.94 Q43879899724.118Q44416233743.95 Q45506725451.94 Q45930014174.95 Q46358708205.110Q4658344367.109 Q4658693003.110 Q47412156653.110Q48867244141.94 Q48965536812.109Q49303179183.94 Q49303289227.95 Q49698585326.111Q49698585326.95 Q49698585326.96 Q49733646878.109Q49919631725.110Q50295957676.93 Q50656923446.94 Q52666267919.95 Q52773753861.95 Q53092503701.109Q53677133549.95 Q569528972.109  Q58797117877.112Q58797117877.96 Q58797117877.97 Q58833082637.110Q60260471301.110Q62025615085.95 Q63417588480.94 Q63589373316.109Q64525772082.94 Q65109593869.95 Q65371908960.94 Q65903965583.94 Q66760123006.109Q66908508420.94 Q67366860043.95 Q67367208235.94 Q67977388214.94 Q68302160783.110Q7192832789.98  Q8182593438.109 Q856114005.109  Q9230853382.112 00000100M00l01H01d02@02\03803W04304O04d05?05[05j06906H06W06f07L07o08R08a09009?09N09O09P09Q09R09^09_09o0:;0:G0:N0:O0:P0:\0:l0;30;60;A0;D0;T0;W0;i0<90<:0<F0<V0<b0<e0=10=40=50=80=90=Q0=R0=U0=a0=e0>10>20>>0>J0>Q0>R0>S0>T0>U0>V0>W0>X0>h0>k0>l0?80?90?:0?F0?I0?J0?V0?Y0?i0@50@60@90@I0@J0@V0@W0@g0A70AC0AM0AY0AZ0Af0B20BR0BU0BX0Bk0C;0CG0CY0Ck0D60D70D80D90D:0D;0D<0D=0D>0D?0DE0DK0DQ0D_0De0E;0ET0EZ0E`0Ef0El0F20F80F>0FD0FJ0FP0FV0Fn0GF0G\0H20HH0HV0Hd0I20IH0IN0IT0IZ0J20J80JN0J\0Je0Jk0K10K70KG0Kf0LB0L^0M60M<0MB0MN0MT0MZ0Mh0N@0NF0NL0Nd0O<0OB0OH0ON0O^0On0P>0PD0P\0Pb0Ph0Pn0Q<0QB0QZ0Q`0R90RO0Re0Rf0S40SL0SR0SX0S^0S_0Se0Sk0T10T70T=0TC0TI0TO0U10U70U=0USFS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2pP2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2pP2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS2ra2sp1A2TB3HB05Ha_st5Hl_stS1R2ra2sp1A2lo3LOS2TBS1R3HIA1h2ra2sp1A2lo3TOP2TBS2ra2sp1A2TB3HB05Ha_st5Hl_stS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2pP3SLO2DS2TB3HB05Ha_st5Hl_stS2sp1A2lo3SLO2DS2TB3HB05Ha_st5Hl_stS2sp1A2lo3SLO2DS2TB3HB05Ha_st5Hl_stS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBS2sp1A2lo2DS2TBFFFFS2ra2sp1A2TBFS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS1A3POSFFS2ra2sp1A2TBS2ra2sp1A3POS2TBS2sp2loS1AS2sp2lo3SLOS1AS2ra2sp1A3POS2TBS1AS1R2lo3LOS3ALO3ACPS2ra2sp1A3POS2TBFS2ra2sp1A2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS1AS2ra2sp1A2TBS1AFS1ASS1R3HIA1h2sp2lo3TOP4HTOPFS1AS2ra2sp1A2TBS2loS2ra2sp1A2TBFS2ra2sp1A2TBS2ra2sp1A2TBS2sp2loFFFFFFFS2ra2sp1A3POS2TBS1AFS2sp1A2lo2DSFFS2ra2sp1A2TBS1AFS2ra2sp1A2TBS1AS1R2lo3LOS3ALO1HS2ra2sp1A2TBFS1AS2ra2sp1A3POS2TBSS2ra2sp1A2TBFS2ra2sp1A3POS2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS1R2lo3LOSS2ra2sp1A2TBFS2ra2sp1A2TBS2ra2sp1A2TBS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AS1AS2sp2lo3SLO3SPR3LO0S2ra2sp1A3POS2TBS2ra2sp1A2TBS2sp1A2lo2TB3x151CS2sp1A2lo2TB3x151CS2sp2lo3SLOFFFFFFFFFS1A2TBS1A2TBS1A2TBS1A3POS2TB3HB0S1A2TBS1A2TB3HB05Ha_st5Hl_stS1A2pP2TB3HB05Ha_st5Hl_stS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS2ra2sp1A3AL83POS3SPR2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stS1A3POS2TB3HB0S1A3POS2TB3HB0S1A3POS2TB3HB0S1A2TB3HB05Ha_st5Hl_stS1A2TBS1A2TBS1A2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TB3HB05Ha_st5Hl_stS1A3POS2TB3HB0S1A2lo2TBS1A2TBS1A2TBS1A2TBS2sp1A2lo3SLO2TBS2sp1A2lo2pP2TB3HB05Ha_st5Hl_stS2sp1A2lo2TB3HB05Ha_st5Hl_stS2sp1A2lo2TB3HB05Ha_st5Hl_stS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS2sp1A2lo2TBS1A2TBS1A2TBS1A3POS2TB3HB0S2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS2ra2sp1A3AL83POS3SPR2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS1A2TBS1A2TB3HB05Ha_stS1A2TB3HB05Ha_stS1A2TB3HB05Ha_stS1A2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS1A2TBS1A3POS2TB3HB0S1A2TBS2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2pP2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stS1A2TB3HB05Ha_st5Hl_stFS1A3POS2TB3HB0S2ra2sp1A3AL83POS3SPR2TBS1A2TBS1A2TBS1A2TBFS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1R2sp1A2lo3LOS3SLO3ALO3ACP3SPR2TBS1A2TBS1A2TBS1A2TB3HB05Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG"] Lemma mxpre13 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_mxpre ()) "Ph,(2>.$4.VR,VHIA,)PLB,(2?.$30.)PLF,(2?.$30.)Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pxa0,(?.&40.)Pxa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)Pxra,(?.&40.)PF,(31.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(19.(?.&8.))PA,$27.Plo,$27.Pidpad,(?.&40.)PpP,(?.&40.)PpA,(?.&40.)PpB,(?.&40.)PpX,(?.&40.)PpY,(?.&40.)PpZ,(?.&40.)PpN,(?.&40.)Phpad,(?.&40.)P,(2=.$4.VR,VHIA,R31.R30.R2?.R<.)P,(32.R=.R<.+=.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(1:.$27.(33.R=.+8.)=)P,(34.=R>.)P,(3.$4.R10.(:.(1>.&40.R31.)-20.)(5.$6.(13.R21.)(5.$6.(13.R2:.)(5.$6.(13.R2;.)(5.$6.(13.R32.)(9.$6.))))))P,(2<.$4.R11.R?.(:.(1>.&40.R32.)-20.))P,(35.(36.VR,)R10.)P,(35.R11.(37.(37.(1>.&40.R34.)+20.)+40.))P,(35.(1>.&40.R35.)(38.$4.VR,VHIA,R39.))P,(1:.$27.(33.(1>.&40.R36.)+10.)=)P,(39.(35.(:.R15.+<0.)R14.)(35.(1>.&40.R37.)R15.))P,(2:.$4.R17.)P,(3:.$4.(21.VR,)(3;.$4.VR,VHIA,R3=.)R18.R17.+<0.)P,(3<.(3=.VR,)(3>.$30.R3=.(3?.R3<.))(36.VR,)(38.$4.VR,VHIA,R3>.)R18.+<0.)P,(1:.$27.(33.(1>.&40.R3<.)+2.)=)(40.$4.(21.VR,)(3;.$4.VR,VHIA,R40.)(41.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+=.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(1;.(1<.R1>.(8.&40.(:.(1>.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(8.&40.R1:.)(8.&40.+=.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(8.&40.(20.(21.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(8.&40.+=13=0.)R1<.(23.(?.&40.))R1;.(24.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. (intros HH dd_H; ddestruct dd_H as (HD & HP & HA & HB & HX & HY & HZ & HN & HT); intros AL8 POS FR ST LOS SLO TOP SPA DS MI OA CWA RAE).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (munch_refl [(A, A + 192); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (lock MI) as MI00.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (A_curve_statics m 13 MI ltac:(clear; lia)) as CS. dpose CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    do 39 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_P end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_P, MIc : mem_inv _ mq_P |- _ =>
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 13)) (cP 13) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 13)) (4 * Z.of_nat (length (cP 13))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 13)) (cP 13) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 13)); vm_compute (Z.of_nat (length (cP 13))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 39 zstep.
    finish; try eassumption; try (clear - SLO; lia).
    all: try (unfold gl_mx_cells; cbv zeta; do 8 (split; [assumption|]); assumption).
    all: match goal with |- ?g => idtac "MXPRE13-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End GLC.

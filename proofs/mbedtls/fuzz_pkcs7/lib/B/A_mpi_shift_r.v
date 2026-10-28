(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_shift_r.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_mpi_core_shift_r.
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
Ltac2 gd_tbl_A_mpi_shift_r () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_shift_r_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_shift_r.mpi_core_shift_r_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_shift_r.A_MPI_CORE_SHIFT_R"; "mpi_shift_r_stmtA"; "A_MPI_SHIFT_R_E"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_shift_r.A_ASAN_MEMSET_SR"].


Definition A_MPI_SHIFT_R_E : Z := 0x9d670.        (* [comment removed for export] *)
Notation MPI_SHIFT_R_STACK_A' := 64 (only parsing). (* [comment removed for export] *)

Definition mpi_shift_r_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (dX : mpd) (count lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_r ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O16.O15.O14.O13.R10.R?.R>.O12.O11.(9.&40.=)R=.R<.R;.R:.R9.R8.R7.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R6.R5.R4.R3.)O6.(:.O16.)O5.(;.(2.&40.))R2.(<.O1<.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.O2.(12.&40.O15.))(>.(?.$10.$10.)(11.$10.$10.(13.O4.)(14.(13.O4.)(15.+4.(16.O4.))))(17.(?.$10.$10.))))O1.R2.)(5.(18.O1<.O1.R2.)(5.(19.O1<.R2.)(5.(1:.O1<.R2.O2.(12.&40.O15.))(5.(1;.O1<.R2.O18.(1<.(1=.O4.)(1>.O4.)(16.O4.)(13.O4.)R1.(1?.O4.)(20.O4.)))(5.(6.$21.(22.(2.&40.)R1.)(22.(2.&40.)(23.O4.)))(5.(6.$10.(24.R1.)(25.(24.(23.O4.))(26.+2.O3.)))(27.O1<.O1;.O1:.O19.O18.O17.R2.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_shift_r_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_r ()) "Ph,(28.O4.O3.O2.)PLB,(4.$29.)PLF,(4.$29.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PdX,$2;.Pcount,$10.Plo,$10.P,(27.O4.O3.O2.R28.R27.R26.R4.)P,(1;.O4.R5.R28.R4.)P,(2<.(6.$2=.(20.R5.)$2>.))P,P,(6.$2=.(20.R6.)$2?.)(30.(14.(13.R7.)(15.+4.(16.R7.)))R5.)P,(19.O4.R8.)P,(5.(30.=R7.)(31.R7.(26.+2.+40.)))P,(1:.O4.R:.R7.(12.&40.R2:.))P,(30.(32.O3.)R8.)P,(30.R9.(33.(33.(12.&40.R2<.)+40.)(34.O3.)))P,(30.(12.&40.R2=.)(35.O4.O3.O2.R31.))P,(6.$10.(36.(12.&40.R2>.)+10.)=)P,(37.(30.(14.(1=.R>.)+10.)R<.)(30.(12.&40.R2?.)(1=.R>.)))P,P,(6.$2=.(20.R?.)$2?.)(37.(30.(14.(1=.R10.)+10.)(13.R10.))(30.(14.(13.R10.)(15.+4.(16.R10.)))(1=.R10.)))P,(38.(39.O3.)(3:.$29.R34.(3;.R33.))(32.O3.)(35.O4.O3.O2.R35.)(13.R10.)(15.+4.(16.R10.)))P,(6.$10.(36.(12.&40.R33.)+2.)=)P,(3<.O4.(3=.O3.)(3>.O4.O3.O2.R37.)R13.(1=.R12.)+10.)P,(6.(2.&40.)R2<.(9.&40.(1=.R13.)))P,(6.(2.&40.)R2<.(9.&40.R13.))(3?.O4.(3=.O3.)(3>.O4.O3.O2.R3:.)(40.O4.O3.O2.R3:.R39.R38.R37.R36.R35.R34.R30.R2?.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R15.R14.R13.R16.)(7.(8.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(9.&40.O1.)R17.(;.(2.&40.))R16.(<.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis CSR : mpi_core_shift_r_stmtA asegs R HIA A_MPI_CORE_SHIFT_R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0260@C12806640203.124C17025492443.123D23181406632.124D31501237935.94 D35881667587.94 D47198685102.124D60109446735.124D64311484648.124K14164087439.124K23023854880.123K29570096888.124K42587433812.94 L11427873569.0  L14161137646.3  L1685717371.0   L19052617798.4  L20092239752.3  L20433961190.90 L23028512581.2  L23100341967.100L2686899723.8   L27155431316.12 L27155463314.6  L27157070640.6  L27157579439.6  L29428324939.5  L29566487709.3  L29767916836.3  L31399144472.93 L31401190584.121L32049487064.120L32049487064.89 L32049487064.93 L33087634096.2  L35653441506.7  L36704614839.3  L37032017814.2  L3830243614.94  L3832291874.122 L38635614367.7  L38635647897.12 L38637653821.8  L38637669026.6  L39543330800.2  L40834179097.92 L41272255311.4  L41274317170.4  L42594106808.2  L43061792393.88 L46122777726.10 L46160487540.92 L46160572444.89 L46748113268.89 L46964343650.3  L5259915527.99  L59308632045.3  L59308632045.4  L59381076118.2  L60098763854.3  L61929803692.92 L62700841801.7  L62700986581.10 L62700990166.8  L62702899572.7  L62702998130.12 L62702998130.13 L66151427842.16 L66151427842.17 L67436452343.4  L67438241365.6  L67438519242.4  L67725521791.3  L67727640898.4  N6320619906.124 N7439670229.124 N7920052297.124 N8683170676.124 O12806640203.124O17025492443.123O27559730561.123O57399310481.124O68505806652.124P14164087439.124P19047445027.123P23023854880.123P46974829030.124Q12370813529.103Q15641191361.122Q15643271421.94 Q15643324129.90 Q17207480672.102Q18694146040.93 Q1950346246.124 Q20414272036.94 Q21798041355.93 Q23181406632.124Q25157988860.93 Q25513505925.93 Q25662358575.93 Q26207421841.93 Q26207688439.91 Q26207721832.94 Q31228709292.93 Q31394594844.93 Q31654082872.93 Q35014437530.93 Q3523383139.103 Q35717497884.93 Q37625145986.102Q38248387216.124Q3834260612.124 Q39212284437.94 Q4143427880.93  Q43879899724.124Q43925228937.94 Q45911940203.91 Q47198685102.124Q49698585326.92 Q53969758199.93 Q5485174314.103 Q5485208735.102 Q58146298210.93 Q60511567613.94 Q60697995187.94 Q6143569392.103 Q61802139820.93 Q6416456232.93  Q64255486968.93 Q67528989526.94 Q8880780715.91  Q9538509144.91  Q9841299618.122 Q9843367298.90  Q9843413918.94  00000100200H01C02002D02a03D03E03F04@05505605705805905I05[05\06006;06<06=06J06K06]06^06g07907^08C08U08g08m09E09R09]0:E0;G0;H0;I0;J0;K0;L0;`0;a0;b0;c0<K0<c0=80=M0=_0=`0>70>@0>P0>W0>a0?80?90?I0?J0?K0?L0?M0?m0?n0?o0@00@10@>0@?0@W0@X0AD0A\0A]0A^0A_0A`0Aa0Ab0B;0B<0Ba0C<0C_0D10DC0DO0Db0E50Ei0Ej0F:0FM0G10G20G>0GJ0GV0Gj0H60HB0HV0ID0IE0IQ0I`0J>0JJ0JK0J]0Ji0K;0KI0Ke0L90LE0LQ0MA0MM0M\0Mh0Mi0N<0N=0Nm0O90OE0P80PV0Q4FFS2ra2sp1X1n1P5limbs2XBS1R5NEEDA2ra2sp1X5limbs2lo3LOS3SLO3SPR2X02XB2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X5limbs3TOP2XB2HB5Ha_st5Hl_stS2ra2sp1X1P5limbs2XBS1R2ra2sp1X1P5limbs2lo3LOS2XBS1R3HIA1h2ra2sp1X1P5limbs2lo3TOP2XBFFS1R3HIA1h2LB2LF2sp1X1n1P5limbs5count2lo3x142XS2XB3x154POSTS1R5NEEDA2ra2sp1X1P5limbs2lo3SLO2XS2XB2HB5Ha_st5Hl_stSFSFS5limbs3xs'4LEN2S2ra2sp1X5limbs2XBFS2ra2sp1X1P5limbs2XBS1n1P2lo2PLFFS1R2sp2lo3SLOFS1R2lo3LOS3ALO3ACPFS1n2NR2N1S2ra2sp1X5limbs2XBS2ra2sp1X1n1P5limbs5count2XB3xs'4LEN2S2ra2sp1X1n1P5limbs5count2XB3xs'4LEN2S2ra2sp1X5limbs2XBS2ra2sp1X5limbs2XBS1n2NRS1R3HIA1h2sp2lo3TOP4HTOPS1n5limbs3LENS5count3CNTS1R5NEEDA2ra2sp1X5limbs2lo3SLO3SPR2X02XBS1R5NEEDA2ra2sp1X1n1P5limbs5count2lo3CNT3SLO3SPR2X02XB2P03xs'4LEN2FFFFSS1R2ra2sp1X5limbs2XBFFFS1R5NEEDA2ra2sp1X5limbs2lo3SLO3SPR2X02XBS2sp1n1P5limbs2lo3LEN2PLS2ra2sp1X5limbs2X02XBS2ra2sp1X5limbs2X02XBS2ra2sp1X5limbs2XBFS2ra2sp1X1P5limbs2X02XBS1n2N12KNS1n5limbs3LEN2KNS2sp2loS1R2lo3LOSS2ra2sp1X1n5limbs2NR2XBFS1R3HIA1h2sp3TOPFFFFS1P2r03PAL1q1r1H2H02q02H42sp3SPAFFFFS1n5limbs3LENFS2sp1X5limbs2lo2XB3x161CFS1R2sp1X1n1P5limbs2lo3LOS3ALO2N12XB2PC3x161CS2sp1X5limbs2lo2XB3x161CFFFFFFS2sp1X1n1P5limbs2lo2XB2PLFS1R5NEEDA2sp1X1n1P5limbs2lo3SLO2XB2PLS2ra2sp1X1P5limbs3XAL2X02XBS2sp1X1n5limbs5count2lo2XB3xs'4LEN2S2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1R1X5limbs4IMG'2XBS1X1n1P5limbs2N12XBS1R5NEEDA2ra2sp1X1n1P5limbs2lo3SLO2XB2HB5Ha_st5Hl_stFS1X1n1P5limbs2XBS1R1X5limbs4IMG'2XBS2ra2sp1X5limbs2lo2XB2HB5Ha_st5Hl_stFS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1R1X5limbs5ALWF'2XBS1X5limbs2XBS1X5limbs2XBS1R1X5limbs5ALWF'2XBS1R5NEEDA2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBFS1X5limbs2XBS1X5limbs2lo2XBS1R5NEEDA2sp1X5limbs2lo3SLO2XBS1X5limbs2XBFS2sp1X5limbs2lo2XBS1X5limbs2XBS2sp1X5limbs2XB2HBS1X1P5limbs2XBS2sp1X5limbs3SPR2XB2HB5Ha_stS1R1X5limbs5ALWF'2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDA2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1X5limbs2XBS1X5limbs2X02XBS1X5limbs2XBFS1R1X5limbs4IMG'2XBFS1R5NEEDA2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1X5limbs2XBS1X5limbs2XBS1R5NEEDA2sp1X1n5limbs5count2lo3CNT3SLO2XB3xs'4LEN2S1R5NEEDA2sp1X5limbs2lo3SLO2XBS1R5NEEDA2sp1X5limbs2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG CSR NEEDA"] Lemma A_mpi_shift_r_walk : mpi_shift_r_stmtA asegs R HIA A_MPI_SHIFT_R_E.
  Proof.
    unfold mpi_shift_r_stmtA, A_MPI_SHIFT_R_E. intros until lo. intros HH MA NST PLO MI CNT ST LOS SLO TOP SPA XS XP CWP RAE OX -> ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    destruct dX as [X sg n P limbs pad own].
    pose proof MA as [(CH & XAL & X0 & LEN & NR & OWN) SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    unfold mpi_cells in CH. unfold MPI_MAX_LIMBS in NR.
    pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 4 * n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep.
    assert (XL7 : Z.land X 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact XAL | clear - XAL; Z.div_mod_to_equations; lia]).
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ X0 XB; rewrite ?Z.mod_small in KZ by lia; lia|].
    zstep. zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA XL7; rewrite ?XL7 in KA; rewrite ?Zmod_0_l in KA; lia|].
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - NR; lia).
    (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NR; lia); rewrite ?unsigned_lit in KN by (clear - NR; lia).
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      match goal with H : stk asegs ?mx lo _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => release_frame FR H (bv_unsigned sp) end.
      zstep.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply evtA_done. unfold mpi_shift_r_postA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      deexists 15. exists limbs.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
      split. { split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [unfold mpi_cells; exact CH|].
        split; [exact XAL|]. split; [exact X0|]. split; [exact LEN|]. split; [unfold MPI_MAX_LIMBS; exact NR|].
        destruct own; [exact OWN| | exfalso; exact (NST eq_refl)]. destruct OWN as (N1 & _). exfalso. clear - N1 KN. lia. }
      split; [reflexivity|].
      split; [destruct limbs; [cbn; rewrite Z.div_0_l; [reflexivity| apply Z.pow_nonzero; clear - CNT; lia]| exfalso; cbn [length] in LEN; clear - LEN KN; lia]|].
      assumption.
    - (* [comment removed for export] *)
      destruct own eqn:EO; [destruct OWN as [_ N0]; exfalso; exact (KN N0)| | exfalso; exact (NST eq_refl)].
      ddestruct OWN as (N1 & PIN & PAL & PX). pose proof (PLO eq_refl) as PL. specialize (XP eq_refl).
      destruct (hm_apart asegs R HIA h LB LF _ HH) as [HF _]. rewrite Forall_forall in HF.
      destruct (HF _ ltac:(apply in_app_iff; left; exact PIN)) as (P0 & _ & PC & _). cbn in P0, PC.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      match goal with H : HM asegs R HIA h LB LF m1 |- _ => rename H into HH1 end.
      pose proof (hm_aobj_block asegs R HIA h LB LF m1 P (4 * n) HH1 PIN) as OP.
      apply (u32arr_transport asegs _ m m1 _ _ PX MU0 WM) in PX || (eapply (u32arr_transport asegs _ m m1) in PX; [| exact MU0| exact WM| cbn [disjoint_from]; clear - PL SLO NEEDA LEN; lia]).
      clear MU0.
      pose proof CSR as SPc. unfold mpi_core_shift_r_stmtA, A_MPI_CORE_SHIFT_R, MPI_CORE_SHIFT_R_STACK_A in SPc.
      callxA_sp (bv_unsigned sp + -16)
        (eapply SPc with (h := h) (LB := LB) (LF := LF) (X := P) (n := n) (cnt := count) (xs := limbs) (lo := lo);
         rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by qlia; try reflexivity; try eassumption;
         first [ clear - N1 NR; lia
               | clear - LEN; lia
               | clear - PAL; Z.div_mod_to_equations; lia
               | clear - SLO NEEDA LOS; lia
               | clear - SPA; Z.div_mod_to_equations; lia
               | left; rewrite LEN; clear - PL SLO NEEDA; lia
               | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
               | clear - TOP SPR SLO NEEDA LOS; lia
               | match goal with |- ?g => idtac "CSR-PRE-LEFT:" g end ]).
      clear SPc.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CSR-SIDE:" g end.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      match goal with H : u32arr asegs m2 P ?xs, H' : length ?xs = length limbs |- _ => rename H into ARR2; rename H' into LEN2; rename xs into xs' end.
      match goal with H : lval xs' n = _ |- _ => rename H into LV2 end.
      match goal with H : HM asegs R HIA h LB LF m2 |- _ => rename H into HH2 end.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      match goal with H : stk asegs ?mx lo _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => release_frame FR H (bv_unsigned sp) end.
      zstep.
      apply evtA_done. unfold mpi_shift_r_postA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      deexists 15. exists xs'.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      assert (LV : limbs_val xs' = limbs_val limbs / 2 ^ count).
      { unfold lval in LV2. rewrite !firstn_all2 in LV2 by (rewrite ?LEN2; clear - LEN; lia). exact LV2. }
      split; [| split; [exact LEN2| split; [exact LV| exact HH2]]].
      split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [| split; [exact XAL| split; [exact X0| split; [rewrite <- LEN; clear - LEN2; lia| split; [unfold MPI_MAX_LIMBS; exact NR|]]]]].
      + unfold mpi_cells. assumption.
      + split; [exact N1|]. split; [exact PIN|]. split; [exact PAL| exact ARR2].
    all: match goal with |- ?g => idtac "SHR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_mpi_shift_r_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_r ()) "PR,$41.PHIA,(42.$43.R1.)P,(44.(3=.R2.))P,(45.$43.R3.R2.$46.)P,(30.=(34.R4.))(47.$43.R5.R4.$48.)")
(* [comment removed for export] *).
Proof. intros. eapply A_mpi_shift_r_walk; eauto. Qed.

Lemma A_mpi_shift_r_spec_closed : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shift_r ()) "PR,$41.PHIA,(42.$43.R1.)P,(44.(3=.R2.))P,(6.$10.(49.R3.)$4:.)P,(30.=(34.R4.))(47.$43.R5.R4.$48.)")
(* [comment removed for export] *).
Proof. intros. eapply A_mpi_shift_r_spec; eauto. eapply A_mpi_core_shift_r_spec; eauto. Qed.

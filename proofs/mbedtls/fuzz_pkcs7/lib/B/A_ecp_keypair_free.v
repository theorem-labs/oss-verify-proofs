(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free P_ecp_group_free P_ecp_keypair_free.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_free A_platform_zeroize A_free_seq A_ecp_group_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_ecp_keypair_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_free.kp_free_LB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_KEYPAIR_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "KF_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "KF_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_free.kp_freed"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ecp_keypair_free_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.ecp_group_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.A_ECP_GROUP_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "ecp_keypair_free_stmtA"; "A_ECP_KEYPAIR_FREE"].


Definition A_ECP_KEYPAIR_FREE : Z := 0xcb2ec.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation ECP_KEYPAIR_FREE_STACK_A := 160 (only parsing).
Definition KF_PHI : Z := GF_PHI + 4 * AVOL_CALL.
Definition KF_FR (d : Z) : Z := GF_FR d + 4 * fr_charge d.

Definition ecp_keypair_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (k : ecp_kp) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_keypair_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1?.O1>.O1=.)Lh',(5.O1?.O1>.O1=.)(6.(7.$0.R13.(8.(9.(:.O18.O17.O16.O15.R12.R11.R10.O14.O13.R?.R>.R=.R<.R;.R:.R9.R8.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R7.R6.R5.R4.)O8.(;.O18.)O7.(<.(2.&40.))R3.(=.O1?.))R2.))(6.(>.O1?.R3.)(6.(?.O1?.R3.O4.(10.&40.O17.))(6.(11.O1.R2.)(6.(12.O1?.O1>.(13.O5.O1:.)O19.(10.&40.O17.)(14.O1>.)(15.O1?.O1>.O1=.O1;.)(16.(17.$18.$18.)(19.$18.$18.O6.(1:.O6.$1;.))(1<.(17.$18.$18.)))O2.R3.)(6.(7.$18.(1=.O1?.O1>.O1=.R1.)(1=.O1?.O1>.O1=.O1;.))(6.(7.$18.(15.O1?.O1>.O1=.R1.)(15.O1?.O1>.O1=.O1;.))(6.(7.$18.(1>.O1?.O1>.O1=.R1.)(1>.O1?.O1>.O1=.O1;.))(6.(1?.O1?.O1>.O1=.R1.R2.)(6.Px,$18.P,(20.O1?.O1>.O1=.O1;.R1.)(20.O1?.O1>.O1=.R3.R2.)(6.(21.(22.O1?.O1>.O1=.R1.)(1:.(22.O1?.O1>.O1=.O1;.)$23.))(6.(21.(24.O1?.O1>.O1=.R1.)(1:.(24.O1?.O1>.O1=.O1;.)(25.O3.)))(6.(26.O1?.O1>.O1=.R1.(13.O5.O1:.)O19.R3.)(27.O1?.O1<.R3.(13.O5.O1:.)O6.(28.O6.O5.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_keypair_free_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_keypair_free ()) "Ph,(5.O5.O4.O3.)PLB,(29.$2:.)PLF,(29.$2:.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PA,$18.Pk,$2<.Plo,$18.Pd,$18.P,(26.O5.O4.O3.R2:.R29.R28.R6.)P,(1?.O5.O4.O3.R2;.R6.)P,(27.O5.O2.R8.R2;.R6.R5.)P,(2=.(2>.R6.))P,(2?.(30.O4.)(31.$2:.(13.R7.R2=.)(32.R2<.))(10.&40.R2:.)(1=.O5.O4.O3.R2>.)R8.$1;.)P,(33.(21.(1:.R9.$1;.)R7.)(21.(10.&40.R2;.)R9.))P,(34.O5.(35.O4.)(20.O5.O4.O3.R30.)R<.R:.$1;.)P,(?.O5.R=.R9.(10.&40.R2=.))P,(21.(14.O4.)R:.)P,(21.R;.(36.(36.(10.&40.R2?.)+:0.)(37.O4.)))P,(21.(10.&40.R30.)(1=.O5.O4.O3.R34.))P,(7.$18.(38.(10.&40.R31.)+10.)=)P,(7.(2.&40.)R30.(39.&40.(3:.O4.)))P,(>.O5.R13.)P,(21.(1:.(22.O5.O4.O3.R38.)$23.)$3;.)P,(3<.O4.R13.$1;.R10.)P,(21.(1:.(24.O5.O4.O3.R3:.)(25.R11.))$3=.)P,(7.(2.&40.)R2?.(39.&40.R15.))(3>.O5.(3?.O5.O4.O3.O2.R3<.R3;.R3:.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.R13.R18.R17.)(8.(9.(:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(39.&40.O1.)R19.(<.(2.&40.))R18.(=.O5.))R17.))")
(* [comment removed for export] *).

Section KPF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variable MT : list modp_ent.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis MPIFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Hypothesis GF : ecp_group_free_stmtA asegs R HIA MT A_ECP_GROUP_FREE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).

  Ltac fsA_in ::= cbn; inl.
  Ltac fsA_addr ::= cbn [md_addr mpd_init];
    match goal with ED : md_addr (kp_d ?k) = _, EX : md_addr (pt_X (kp_Q ?k)) = _, EY : md_addr (pt_Y (kp_Q ?k)) = _, EZ : md_addr (pt_Z (kp_Q ?k)) = _ |- _ =>
      rewrite ?ED, ?EX, ?EY, ?EZ | _ => idtac end.

  Ltac kfA_free1 spo md X rest :=
    lazymatch goal with
    | HH : HM _ _ _ ?xhc ?xLBc _ ?xmc, PXA : presW _ _ _ ?xh0 ?xLBf _ ?xSP _ [(?xA, _)] ?xm0 _, UWO : uw_obj _ _ 256 ?xd, ST : stk _ _ ?xlo _,
      HBR : blkfacts _ (?xLB ++ _), DISF : mpds_apart ?xFR |- _ =>
        eapply (free_stepA R HIA A_MPI_FREE MPIFREE NEEDR DIMG) with
          (d0 := md) (X0 := X) (A := xA) (sz := 256) (d := xd) (SP := xSP) (h0 := xh0) (m0 := xm0) (LBf := xLBf) (lo := xlo) (LBall := xLB) (FR := xFR);
        [ fsA_side spo rest .. | ]
    end;
    lazymatch goal with
    | |- forall _, _ =>
        lazymatch goal with HH : HM _ _ _ _ _ _ _, LIV : Forall (mpdr_at _ _ _) _, CH : Forall _ _, PXA : presW _ _ _ _ _ _ _ _ _ _ _,
                            HTc : htop _ _ _ _ = _, HSc : hstkhi _ _ _ _ = _, HFc : hflag _ _ _ _ = _, HCSc : (forall x, hcs _ _ _ _ x -> hcs _ _ _ _ x),
                            HV : havol _ _ _ _ <= _, HFR : hfr _ _ _ _ <= _, OBJ : aobj _ _ _ _ _ 256, ST : stk _ _ _ _, MI : mem_inv _ _ |- _ =>
          fsA_post HH HTc HSc HFc HCSc HV HFR LIV CH PXA OBJ ST MI
        end
    | |- ?gg => idtac "kfA_free1: free_stepA left goal" gg
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "02?0@D13156179990.113D31501237935.112D35881667587.112D35881667587.113L10305806636.4  L11287912535.139L1144623966.157 L11774327555.109L12286612363.7  L12288290349.5  L12288437416.4  L1261479139.1   L13127733540.193L13131993161.139L13132193737.157L13132193737.175L13198012894.139L13592035095.2  L14397133912.139L14397332440.157L1555092503.2   L17398248931.1  L18426875374.102L19457554581.193L19956363751.157L20421528774.147L20431817446.194L20433961190.108L22706556809.3  L22725723689.9  L2351528779.157 L2351528779.175 L2351854795.139 L2364372390.193 L23893409987.7  L25850704359.175L26793006514.3  L26892149748.193L27483706604.139L27484167020.157L27484167020.175L28814043710.109L29149025057.0  L29898465545.3  L30993508591.157L30993508591.175L30993573743.139L30997964290.193L31399144472.193L31564742106.175L32049487064.108L32049487064.194L3318502618.157 L33306151620.157L33306151620.175L33306215748.139L33318994985.193L34061135516.1  L34709680856.157L34709680856.175L34709749080.139L34751889498.139L347726353.1    L3523383060.9   L3538062819.157 L3538062819.175 L3538062819.193 L3538256483.139 L35653441506.7  L36184245428.1  L36837110646.7  L37714553091.1  L3832472834.194 L38660161058.193L38664159055.139L38664614095.157L38664614095.175L39010876474.219L39972690504.6  L40281191306.3  L41596348845.7  L41598571912.8  L43055340993.106L43408555890.3  L4574513722.219 L45797812147.193L46202318359.2  L46460681476.4  L46550781791.157L46550781791.175L46748113268.108L48132467214.7  L48580193912.175L49530003784.1  L49542659165.139L49543115741.157L49543115741.175L50543465527.193L51305814964.1  L53113130784.5  L55978761415.193L56552377779.109L56552377779.194L5676486753.139 L57842889822.175L58238699799.2  L59308628179.3  L59377936871.193L60098763854.3  L62018535662.1  L62705181399.5  L63799197048.6  L65439589905.1  L66151427842.16 L66748138130.6  L67431951009.157L67431951009.175L67432277281.139L9568782640.5   Q13296972522.110Q14525642139.112Q15641306337.194Q15643324129.108Q20685106778.113Q22712450012.112Q22712450012.113Q25513505925.111Q25513505925.112Q34362328320.112Q34362328320.113Q36801578553.112Q3830427394.109 Q3832472834.194 Q45914037331.109Q49698585326.110Q49698585326.111Q51233783137.194Q51235796833.109Q58146298210.111Q67528989526.112Q67528989526.113Q9841186690.194 Q9843367298.108 00000f01\02E02n03:03C03L03U03m04604?04B04K04T04]04f04o05605?05H05O05R05[05d05m06606?06H06P06h06i06j06k07@07O07X07a07j08M09009S09`09a09j0:U0;@0;k0<40<=0<F0<O0<X0<a0=30=E0=W0=i0=m0>60>?0>H0>Q0>T0?70?T0@10@N0@k0AE0AH0AT0AW0B70BO0BP0BQ0BR0B[0C20C;0CG0C^0D>0DG0DP0DY0D`0Dm0EB0EW0E`0F;0FD0FH0FQ0FZ0Fc0Fl0Fo0G>0GG0GP0GY0Gn0H70H>0HH0HQ0H[0H^0I00IB0IE0Ie0J80JY0K:0K[0Kh0L40Lf0M20M>0N00NK0Nf0OD0Ob0Oc0Od0PN0Pf0Q>0QJ0Q`0R60RB0RN0S80Sb0TL0Td0U<S1R5NEEDR2sp2s01A2lo3LOS3SLO3SPR3POS2KB2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1A2lo3LOS3SLO3SPR3POS2KB2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1A5SPTOP2KB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01A5SPTOP2KB2HB5Ha_st5Hl_stS2sp1A2lo2SXS2sp1A2KBS2sp1A2KBS2sp1A2KBS1R5NEEDR2sp1A2lo2SX3SLOS1A2dd2I5S1A2dd2B1S1AS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS1A3POSS2sp1A2KBS2sp1A2KBS1A3POSS1AS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS1A1x2HxS1R2sp2lo3LOS3ALO1a1n2HnFFFS1R3HIA1h2sp1A3BUD2KBS1A2dd2B12d'2H0S2sp1A2KBS1A2dd2B1S2sp1A2KBS1R3HIA1h2sp1A1d4BUDF3SPR2D03POS2KBS1R3HIA1h2sp1A1d4BUDF3SPR2D03POS2KBS1R3HIA1h2sp1A1d4BUDF3SPR2D03POS2KBS2sp1A3POS2KBSS1A2dd2B2S2sp1A2KB1R5NEEDR2lo2SX3SLO3SPA3SPR3AL83POSS2sp1A2KB1R5NEEDR2lo2SX3SLO3SPA3SPR3AL83POSS1R5NEEDR2sp1A2lo2SX3SLO3SPA3SPR3AL83POS2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS1R2sp1A2lo3SLO2KBS1R2sp1A2lo3SLO2KBS1R2sp1A2lo3SLO2KBS1R2sp1A2lo3SLO2KBS2spS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS1AS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACP3SPRS1R2sp1A3ACV3SPR3POS2KB5ACLspS1R2sp1A3ACV3SPR3POS2KB5ACLspS1R2sp1A3ACV3SPR3POS2KB5ACLspS1R2sp1A3ACV3SPR3POS2KB5ACLspS1R3HIA1h2sp2lo5SPTOP4HTOPS1AS2sp1A2lo2SXS1AS1R5NEEDR2sp1A2lo3SLO3SPR3POS2KBS1R3HIA1h2sp1A1d4BUDF2KBFFFS2sp1A2KBS1R5NEEDR2sp2lo3LOS3SLOS1R3HIA1hS2sp1A2lo2SXS1R2sp2lo3LOS3ALO2dd2I4S1R5NEEDR2sp1A2lo3SLO3SPR3POS2KBS2dd1x2HxS2sp1A2KBS2sp1A2KBS1A3POSS1R3HIA1h3BUDS1R3HIA1h2sp1A3BUD2KBS1R3HIA1h2sp1A3BUD2KBS2sp1A2KBS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1A2KBS2spS2sp1A2KBS2sp1A2KBS2sp1A2KBS2sp1A2KBS1AS1R3HIA1h2h42HVS2sp1A2KBS2sp1A2KBS2sp1A2KBS1R3HIA1h2sp1A3BUD2KBS2sp1A2KBS1A3POSS1A3POS2K0S2sp1A2KBS1R2lo3LOSS1RS1R3HIA1h2sp5SPTOPS1R3HIA1h1d2h43HFRS1AS2sp2r03SPA1q1r1H2H02q02H41A3AL8S1R3HIA1h1d4BUDF2D0S1R2sp1A3SPA3ACV3SPR3POS2KB5ACLspS1R2sp1A3SPA3ACV3SPR3POS2KB5ACLspS1R2sp1A3SPA3ACV3SPR3POS2KB5ACLspS1R2sp2lo3SLOS2sp1A2KB2HBS1R5NEEDR2ra2sp1A2lo3LOS3SLO3ALO2KB2HB5Ha_st5Hl_stS2sp1A2lo2KBS2sp1A2lo2KBS1R5NEEDR2sp2s01A2lo3LOS3SLO3ALO2KB2HB5Ha_st5Hl_stS2ra2sp1A2KB2HB5Ha_st5Hl_stS2sp2s01A2KB2HB5Ha_st5Hl_stS2ra2sp1A2lo2KB2HB5Ha_st5Hl_stS2sp2s01A2lo2KB2HB5Ha_st5Hl_stFFS1R5NEEDR2sp2s01A2lo3SLO2KB2HB5Ha_st5Hl_stS1R5NEEDR2sp1A2lo3SLO2KBS1R5NEEDR2sp1A2lo3SLO2KBS2sp1A2KB2HBS2sp1A3SPR2KB2HB5Ha_stS2sp1A3SPR2KB2HB5Ha_stS2sp1A2lo2KBS2sp1A2lo2KBS1R5NEEDR2ra2sp1A2lo3SLO2KB2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1A2lo3SLO2KB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01A2lo3SLO2KB2HB5Ha_st5Hl_stS1R5NEEDR2sp1A2lo3SLO2KBS1R5NEEDR2sp1A2lo3SLO2KB". (* [comment removed for export] *)
  #[using="MPIFREE GF NEEDR DIMG HMND"] Lemma A_ecp_keypair_free_walk : ecp_keypair_free_stmtA asegs R HIA MT A_ECP_KEYPAIR_FREE.
  Proof.
    unfold ecp_keypair_free_stmtA, A_ECP_KEYPAIR_FREE. intros until d.
    intros HH HK0 K DIS CW SX OBJ ST LOS SLO SPTOP SPA TP MI BUD UWO BUDF ->.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof (HMND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2]. pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR HAP]. change (blkfacts L (LB ++ LF)) in HBR.
    unfold ECP_KEYPAIR_SIZE in CW, SX, OBJ, UWO.
    ddestruct K as (G & ED & MD & FD & (EX & EY & EZ & MX & MY & MZ) & FQ).
    dpose G as (_ & AL8 & POS & _).
    pose proof MZ as (CHZ & _). unfold mpdr_at in CHZ. rewrite EZ in CHZ. pose proof (rw_cells_bound _ _ _ _ CHZ) as KB. cbn [cells_size csize Nat.add length mpi_cells] in KB. clear CHZ.
    set (g := kp_grp k) in *. set (LBg := grp_free_LB g LB).
    assert (SUBg : forall b, In b LBg -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    assert (SUBF : forall b, In b (kp_free_LB k LB) -> In b LB) by (intros b Hb; apply SUBg; eapply lb_free_mpds_sub; exact Hb).
    set (FRL := kp_tail_mpds k) in *.
    assert (DISF : mpds_apart FRL) by (eapply mpds_apart_sub; [exact DIS| intros dd Hd; apply kp_mpds_tail; exact Hd]).
    assert (FRB : Forall mpd_freeable [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)]) by (constructor; [exact FD| exact FQ]).
    assert (NI : forall dd, In dd FRL -> md_own dd = LHeap -> ~ In (md_p dd, 4 * md_n dd) (kp_free_LB k LB)).
    { intros dd Hd O. unfold kp_free_LB. apply lb_free_mpds_notin; [| exact Hd| exact O]. unfold grp_free_LB. apply lb_free_mpds_nodup. exact NDL. }
    assert (ACLsp : alloc_ceiling <= bv_unsigned sp) by (clear - ALO LOS SLO NEEDR; lia).
    pose proof (free_facts_introA asegs R HIA h LB LF (kp_free_LB k LB) m (bv_unsigned sp) _ A 256 FRL HH NDL
                  ltac:(intros dd Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; assumption) CW SUBF NI ACLsp ltac:(lia) DI1 DI2) as FF1.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (presW_sub_blocks asegs R HIA h LB (kp_free_LB k LB) LF (bv_unsigned sp) (arl_stklo R) [(A, A + 256)] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 256)] HH ltac:(clear; lia)) SUBF) as PXA.
    pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (conj MI I) as MIbox. pose proof (conj G (conj MD (conj MX (conj MY MZ)))) as Gbox. clear G MD MX MY MZ.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - POS KB; lia); clear - K0 POS; lia|]. clear K0.
    (* [comment removed for export] *)
    assert (AL7 : Z.land A 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact AL8 | clear - AL8; Z.div_mod_to_equations; lia]).
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct MIbox as [MIm _]. ddestruct Gbox as (G & MD & MX & MY & MZ).
    assert (G1 : ecp_group_at asegs MT m1 LB A g).
    { eapply ecp_group_at_munch; [exact G| exact MU0| exact WM0| exact MIm| assumption| cbn; clear - SX ALO LOS; lia|].
      intros dd Hd O. ddestruct (mpdr_blk_factsA asegs L m LB (LB ++ LF) dd) as (_ & _ & I3 & I4 & _); [| exact O| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| cbn; clear - I3 I4 ALO LOS; lia].
      ddestruct G as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX' & MY' & MZ') & MN & _).
      unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    assert (LIV : Forall (mpdr_at asegs m1 LB) [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)]).
    { eapply (lives_munchA asegs L m m1 LB (LB ++ LF)); [| exact MU0| exact WM0| exact MIm| assumption| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| | intros a n Ha Hn; cbn; clear - Ha Hn ALO LOS; lia].
      - repeat apply Forall_cons; try apply Forall_nil; assumption.
      - repeat apply Forall_cons; try apply Forall_nil; rewrite ?ED, ?EX, ?EY, ?EZ; cbn; clear - SX ALO LOS; lia. }
    clear MU0 WM0 MIm G MD MX MY MZ.
    (* [comment removed for export] *)
    zstep.
    pose proof GF as SG. unfold ecp_group_free_stmtA, A_ECP_GROUP_FREE, ECP_GROUP_SIZE in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG with (h := h) (LB := LB) (LF := LF) (A := A) (g := g) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by (clear - SPR SLO NEEDR LOS ALO ACP; lia);
        first [ exact HK1 | exact G1 | exact LOS | exact TP | reflexivity
              | lazymatch goal with
                | |- HM _ _ _ h LB LF _ => assumption
                | |- mpds_apart _ => eapply mpds_apart_sub; [exact DIS| intros dd Hd; apply kp_mpds_grp; exact Hd]
                | |- client_wrange _ _ _ _ A 192 =>
                    eapply (client_wrange_weak L); [exact CW| | clear; lia| clear; lia| clear; lia];
                    apply lb_sub_app; intros b Hb; change (In b LBg); unfold kp_free_LB in Hb; eapply lb_free_mpds_sub; exact Hb
                | |- A + 192 <= lo \/ _ => clear - SX; lia
                | |- aobj _ _ _ _ A 192 => eapply aobj_sub; [eassumption| clear; lia| clear; lia]
                | |- stk _ _ lo _ => assumption
                | |- lo <= _ => clear - SLO NEEDR; lia
                | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- mem_inv _ _ => assumption
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold KF_PHI in BUD; unfold GF_PHI, AVOL_CALL in *; clear - BUD; lia
                | |- uw_obj _ A 192 d => eapply uw_obj_sub; [exact UWO| clear; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold KF_FR in BUDF; unfold GF_FR, fr_charge in *; clear - BUDF D0; lia
                end
              | match goal with |- ?gg => idtac "GF-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXg & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & GZ & GZC).
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST2, PXg by (clear - SPR SLO NEEDR LOS ALO ACP; lia).
    unfold ECP_GROUP_SIZE in PXg. change (grp_free_LB g LB) with LBg in HH2, GZ, PXg.
    replace (ret_pc (Z_to_bv 64 0xcb30c)) with (Z_to_bv 64 0xcb30c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (GIN' : forall dd, In dd (grp_free_mpds g) -> In dd (grp_mpds g)).
    { intros dd Hd. unfold grp_free_mpds in Hd. unfold grp_mpds. destruct (g_h g =? 1); [destruct Hd|]. destruct (g_h g =? 2); cbn in Hd |- *; tauto. }
    (* [comment removed for export] *)
    assert (LIV2 : Forall (mpdr_at asegs m2 LBg) [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)]).
    { eapply Forall_impl; [| eapply Forall_and; [exact LIV| ]].
      2:{ instantiate (1 := fun dd => In dd FRL /\ A + 192 <= md_addr dd /\ md_addr dd + 16 <= A + 256).
          repeat apply Forall_cons; try apply Forall_nil; rewrite ?ED, ?EX, ?EY, ?EZ; cbn -[FRL]; (split; [subst FRL; cbn; tauto| clear; lia]). }
      cbv beta. intros dd [Md (Hd & B1 & B2)].
      eapply (mpdr_at_presA asegs L m1 m2) with (LBX := LBg ++ fdata LF); [exact Md| exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXg)| assumption| exact MI2| | |].
      - eapply (client_range_of_wrange L); [exact CW| apply lb_sub_app; intros b Hb; change (In b LBg); unfold kp_free_LB in Hb; eapply lb_free_mpds_sub; exact Hb| clear; lia| clear - B1; lia| clear - B2; lia].
      - cbn. clear - B1 B2. lia.
      - intros O. ddestruct (FF1 dd Hd O) as (I1 & I2 & I3 & I4 & I5).
        assert (KEEPd : In (md_p dd, 4 * md_n dd) LBg).
        { subst LBg. unfold grp_free_LB. apply lb_free_mpds_keep; [exact I1|]. intros d' Hd' O' E'.
          apply (DIS dd d'); [apply kp_mpds_tail; exact Hd| apply kp_mpds_grp, GIN', Hd'| | exact O| exact O'| exact E'].
          pose proof (grp_mpds_addr _ _ _ _ _ _ _ G1 ltac:(apply GIN'; exact Hd')) as [? ?]. clear - B1 B2 H H0. lia. }
        split; [exact KEEPd|]. split; [intros x Hx; right; right; exists (md_p dd, 4 * md_n dd); split; [apply in_app_iff; left; exact KEEPd| cbn; clear - Hx; lia]| cbn; clear - I5 B1 B2; lia]. }
    lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -16) _ |- _ =>
      pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ PXg FRx ltac:(apply client_range_stack; cbn; clear; lia) ltac:(cbn; clear - SX SLO NEEDR; lia)) as FR2; clear FRx end.
    assert (PXA2 : presW asegs R HIA h (kp_free_LB k LB) LF (bv_unsigned sp) (arl_stklo R) [(A, A + 256)] m m2).
    { eapply presW_call; [exact PXA| exact PXg| intros b Hb; change (In b LBg); unfold kp_free_LB in Hb; eapply lb_free_mpds_sub; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
      intros x Hx. cbn in Hx |- *. clear - Hx. lia. }
    assert (OBJ2 : aobj asegs AL (hcs asegs R HIA h) m2 A 256).
    { lazymatch goal with OBJx : aobj _ _ (hcs _ _ _ h) m1 A 256 |- _ =>
        eapply (presA_aobj asegs R (hcs asegs R HIA h)); [exact CSOK| exact PXg| exact OBJx| | clear - LOS SLO NEEDR; lia| intros x Hx; eapply hcs_below_top; exact Hx] end.
      eapply (client_range_of_wrange L); [exact CW| apply lb_sub_app; intros b Hb; change (In b LBg); unfold kp_free_LB in Hb; eapply lb_free_mpds_sub; exact Hb| clear; lia| clear; lia| clear; lia]. }
    assert (CH : Forall (fun ac => rw_cells asegs m2 (fst ac) (snd ac)) [(A, [CB 192 (repeat (Z_to_bv 8 0) 192)]); (bv_unsigned sp - 16, [C8 s0; C8 ra])]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [exact GZC| replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact FR2]. }
    clear LIV PXA GZ GZC PXg G1 FR2 SG.
    repeat match goal with H : aobj _ _ _ m1 _ _ |- _ => clear H | H : stk _ m1 _ _ |- _ => clear H | H : mem_inv _ m1 |- _ => clear H | H : HM _ _ _ _ _ _ m1 |- _ => clear H
                         | H : ainv_laws _ _ |- _ => clear H | H : kinv_laws _ _ _ |- _ => clear H | H : crange (hcs _ _ _ _) _ _ |- _ => clear H | H : cs_ok _ _ |- _ => clear H end.
    rename LIV2 into LIV. rename PXA2 into PXA. rename OBJ2 into OBJ. rename HH2 into HH. rename ST2 into ST. rename MI2 into MI.
    rename HT2 into HTc. rename HS2 into HSc. rename HF2 into HFc. rename HCS2 into HCSc. rename HV2 into HV. rename HFR2 into HFR.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_ok asegs R HIA h2) as CSOKc.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof (crange_mono _ _ _ _ HCSc SCS) as SCSc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJ) as OBJc.
    unfold KF_PHI in BUD. unfold KF_FR in BUDF.
    (* [comment removed for export] *)
    zstep. zstep. kfA_free1 (bv_unsigned sp + -16) (kp_d k) (A + 192) [pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)].
    zstep. zstep. kfA_free1 (bv_unsigned sp + -16) (pt_X (kp_Q k)) (A + 208) [pt_Y (kp_Q k); pt_Z (kp_Q k)].
    zstep. zstep. kfA_free1 (bv_unsigned sp + -16) (pt_Y (kp_Q k)) (A + 224) [pt_Z (kp_Q k)].
    (* [comment removed for export] *)
    fa_get CH 4%nat CFR. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) in CFR by lia.
    zstep. zstep. zstep. zstep. release_frame CFR ST (bv_unsigned sp).
    try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    lazymatch type of CH with Forall ?P ?CS =>
      let pre := eval cbn [removelast] in (removelast CS) in
      assert (CH' : Forall P pre) by (apply (proj1 (proj1 (Forall_app P pre [(bv_unsigned sp - 16, [C8 s0; C8 ra])]) CH)));
      clear CH; rename CH' into CH end.
    zstep. kfA_free1 (bv_unsigned sp) (pt_Z (kp_Q k)) (A + 240) ([] : list mpd).
    (* [comment removed for export] *)
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold ecp_keypair_free_postA. deexists 15.
    lazymatch goal with HH : HM _ _ _ ?hf _ _ ?mf |- _ => exists mf, mo9, hf end.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF9|].
    split; [unfold ECP_KEYPAIR_SIZE; exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ PXA)|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
    split; [unfold KF_PHI; clear - HV; lia|]. split; [unfold KF_FR; clear - HFR; lia|].
    split. { lazymatch type of HH with HM _ _ _ _ ?l _ _ => change l with (kp_free_LB k LB) in HH end. exact HH. }
    fa_get CH 0%nat CQZ. fa_get CH 1%nat CQY. fa_get CH 2%nat CQX. fa_get CH 3%nat CD. fa_get CH 4%nat CG.
    unfold ecp_keypair_at, kp_freed. cbn [kp_grp kp_d kp_Q md_addr mpd_init].
    split; [apply ecp_group_at_zero; [exact CG| exact AL8| exact POS]|].
    split; [reflexivity|]. split; [apply mpdr_at_init; [exact CD| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia]|]. split; [cbn; discriminate|].
    split; [| unfold pt_freeable, pt_mpds; cbn; repeat constructor; cbn; discriminate].
    unfold ecp_point_at, pt_init; cbn [pt_X pt_Y pt_Z md_addr mpd_init].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    replace (A + 208 + 16) with (A + 224) by lia. replace (A + 208 + 32) with (A + 240) by lia.
    split; [| split]; (apply mpdr_at_init; [assumption| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End KPF.

Lemma A_ecp_keypair_free_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_keypair_free ()) "PR,$40.PHIA,(41.$42.R1.)PMT,(29.$43.)P,(44.(35.R3.))P,(45.$42.R4.R3.$46.)P,(47.$42.R5.R4.R3.$48.)P,(21.=(37.R6.))P,(6.(21.(49.(30.R7.))(4:.(30.R7.)))(21.(4;.(30.R7.))(4<.(30.R7.))))P,Ph,(5.$42.R8.R7.)PLB,(29.$2:.)PLF,(29.$2:.)Pm,P,(2.&40.)(3.(2.&8.))P,(26.$42.R<.R;.R4.R3.R2.R1.)(4=.$18.(4>.(17.$18.$18.)$18.(4?.$18.$18.)R4.))(50.$42.R9.R8.R7.$51.)")
(* [comment removed for export] *).
Proof. intros. eapply A_ecp_keypair_free_walk; eauto. Qed.

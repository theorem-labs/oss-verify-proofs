(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_amem_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
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
Ltac2 gd_tbl_A_bcmp () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.B.A_rip.rip_consts"; "Walk.micP_post"; "Walk.micQ_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.length"; "Walk.mic_consts"; "Walk.micpt_post"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record mic_consts (m : mem) : Prop := {
    mc_cf : ro_cells asegs m 0x0f5e40 [C8 (Z_to_bv 64 0x19b528)];     (* [comment removed for export] *)
    mc_icm : ro_cells asegs m 0x19b626 [C1 (Z_to_bv 8 1)];            (* [comment removed for export] *)
    mc_scm : ro_cells asegs m 0x19b627 [C1 (Z_to_bv 8 1)];            (* [comment removed for export] *)
    mc_inited : ro_cells asegs m 0x10a6d8 [C1 (Z_to_bv 8 1)];         (* [comment removed for export] *)
    mc_rmemcmp : ro_cells asegs m 0x0f7b80 [C8 (Z_to_bv 64 0x0ea990)];(* [comment removed for export] *)
    mc_rbcmp : ro_cells asegs m 0x0f7b88 [C8 (Z_to_bv 64 0x0ea8c0)];  (* [comment removed for export] *)
    mc_rip : rip_consts m
  }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L12633578871.20L13809535095.20L21043402967.20L26640887415.20L26986573175.20L35984829559.2000000:00D00N00X00b00lS2lo2hi2LOS2lo2hi2LOS2lo2hi2LOS2lo2hi2LOS2lo2hi2LOS2lo2hi2LO". (* [comment removed for export] *)
  #[using="Type"] Lemma mic_consts_munch : forall lo hi m m',
    munch [(lo, hi)] m m' -> HSE < lo -> mic_consts m -> mic_consts m'.
  Proof.
    intros lo hi m m' MU LO [R1 R2 R3 R4 R5 R6 RC].
    split; [ .. | eapply rip_consts_munch; eauto];
      (eapply ro_cells_transport; [eassumption | exact MU | cbn; split; [lia | exact I]]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L12055610268.50L16405147374.59L29644601389.59L30095897756.55L35469551417.59L44373685212.50L48379326627.59L53520163529.59L53520247005.59L56775215785.59L56775393469.59Q17581378383.58Q35222541774.58Q39502766003.58Q4111067988.58 Q52324771135.5800001d02702D02Z02m04a04k05I05j06H06i07?07@07P07d08>S2AL2CS1q2ra2sp2gp2tp2t02t12t22s02s12a02a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo1p2a32a42Hk2HpS1k1q2lo1p2Hk2Hp2NES1k1q1p2Hk2NES1k1q2lo2hi1p2Hk2Hp2HqS1k1q2lo1p2Hk2Hp2EQS2AL2CS1q2ra2sp2gp2tp2t02t12t22s02s12a02a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo1p2a32a42Hk2HpS1k1q1p2HkS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3HloS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3Hlo2EQS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3HloS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3Hlo2EQS1k1q2lo2hi1p2Hk2Hp2HqFS1k1q2lo1p2Hk2HpS1k1q2lo1p2Hk2Hp3HloS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma mic_orloop : ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Ppc,$0.Pk,$1.Pp,$0.Pq,$0.Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))Plo,$0.Phi,$0.P,(5.(6.$0.R26.+5993<.)(6.$0.R26.+59:48.))P,(7.(8.R24.R25.)(9.R26.))P,(:.(7.R4.R26.)(;.R26.R25.))P,(7.R26.R4.)P,(;.R5.(<.+2.+3?.))P,(7.=R7.)P,Px,$0.P,(:.(7.R9.R1.)(;.R1.R8.))(=.(2.&8.)Lb,(2.&8.)(>.$?.R<.R3.(10.(2.&8.)R1.(11.(2.&8.)))))P,Px,$0.P,(:.(7.R:.R1.)(;.R1.R9.))(12.VAL,VCS,R2.)(13.$?.VAL,VCS,Lms',$14.(=.(2.&40.)La3',(2.&40.)(=.(2.&40.)La4',(2.&40.)(6.$14.R3.(15.(16.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.(17.&40.R2>.)(17.&40.R2>.)R2.R1.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(17.&40.(18.R31.+10.))R?.(19.(2.&40.))R>.(1:.$?.)))))(15.(16.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(17.&40.R2<.)(17.&40.R2;.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(17.&40.R2>.)R<.(19.(2.&40.))R;.(1:.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros pc k. intros until hi. intros PC.
    destruct PC as [-> | ->];
      [ replace (366908 + 16) with 366924 by reflexivity | replace (367176 + 16) with 367192 by reflexivity ]; revert p a3 a4;
      (induction k as [|k IH]; intros p a3 a4 Hk Hp Hq Hhi Hlo RD AOK; [lia|]; al_facts;
       destruct (RD p ltac:(lia)) as [b B]; pose proof (bytes_at_read1 _ _ _ _ B) as RDB;
       zstep; zstep; zstep; zstep;
       destruct (Z.eq_dec (p + 1) q) as [EQ|NE];
       [ if_falseU; rewrite EQ; finish
       | if_trueU; eapply IH; try eassumption; lia ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac qc_block11 X n E0 E1 :=
    do 11 zstep;
    rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
    replace (X + n + -1) with (X + n - 1) by lia;
    rewrite !Z.mod_small by lia;
    rewrite !land_m8 by lia; rewrite !hull_sh by lia;
    rewrite E0, E1.

  Definition micP_post (sp gp tp s0 a0 s2 s3 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Lms',$14.(=.(2.&40.)Lra,(2.&40.)(=.(2.&40.)Lt0,(2.&40.)(=.(2.&40.)Lt1,(2.&40.)(=.(2.&40.)Lt2,(2.&40.)(=.(2.&40.)La1,(2.&40.)(=.(2.&40.)La2,(2.&40.)(=.(2.&40.)La3,(2.&40.)(=.(2.&40.)La4,(2.&40.)(=.(2.&40.)La5,(2.&40.)(=.(2.&40.)La6,(2.&40.)(=.(2.&40.)La7,(2.&40.)(=.(2.&40.)Ls6,(2.&40.)(=.(2.&40.)Ls10,(2.&40.)(=.(2.&40.)Lt3,(2.&40.)(=.(2.&40.)Lt4,(2.&40.)(=.(2.&40.)Lt5,(2.&40.)(=.(2.&40.)Lt6,(2.&40.)(=.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(:.(6.$14.R13.(15.(16.R12.O11.O10.O?.R11.R10.R?.O>.(17.&40.O3.)O=.R>.R=.R<.R;.R:.R9.R8.O<.O;.(17.&40.O4.)O:.R7.O9.O8.(17.&40.(18.O3.-41.))R6.O7.R5.R4.R3.R2.)O6.(17.&40.+59584.)O5.(19.(2.&40.))R1.(1:.$?.)))(:.(1;.(10.(1<.$0.$0.)(1=.$0.$0.O2.(1>.&40.O11.))(11.(1<.$0.$0.)))O1.R1.)(:.(1?.$?.O1.R1.)(:.(20.$?.R1.)(21.$?.R1.O2.(1>.&40.O11.))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@C17025492443.113C17025492443.88 L11447729190.144L11671109536.86 L11944109973.88 L14345069909.69 L17423148388.92 L1952302740.87  L1956510917.72  L19628431903.90 L20966712717.92 L24122754266.92 L24122936649.92 L24124928684.86 L24124928684.87 L24608617390.70 L24982526223.90 L25727469113.56 L25792253067.68 L27196467039.69 L28083348026.88 L29739405618.87 L29784464483.91 L29786564236.87 L29971684470.70 L31686803170.92 L3248729870.2   L33139774177.92 L34120414369.0  L3421674955.92  L34922678286.2  L36929494798.2  L38150352304.92 L39594679749.87 L45607281678.2  L46817748388.72 L47543971773.92 L49899794702.2  L50296483778.92 L51172192526.2  L52065394884.86 L52514161039.90 L53517158443.69 L53519158063.90 L58873582488.87 L61097676998.2  L61932014891.69 L64596837268.70 L66488557582.2  L7106453518.2   L9963543243.72  O14206727921.113O14206727921.88 O15547502833.113O15547502833.88 O17025492443.113O17025492443.88 O23485702385.113O23485702385.88 O32131581681.113O32131581681.88 O38504098033.113O38504098033.88 O4492316913.113 O4492316913.88  O48978854641.113O48978854641.88 O65485481713.113O65485481713.88 P3245129067.113 P3245129067.88  P34917767787.113P34917767787.88 P36941614443.113P36941614443.88 P45611546219.113P45611546219.88 P49904706411.113P49904706411.88 P51184575339.113P51184575339.88 P66501341803.113P66501341803.88 P7102853739.113 P7102853739.88  Q14673372720.87 Q15643823314.87 Q16263154483.87 Q19275945964.87 Q21773766844.87 Q21797814763.87 Q22349224071.88 Q23650890746.91 Q24745328269.91 Q26151546087.91 Q28218390483.91 Q29427030349.87 Q31394395900.87 Q34268098539.87 Q34501421650.87 Q34947676851.87 Q36722057835.87 Q3742509637.87  Q38148316102.87 Q39778974580.87 Q39942779359.87 Q40886982406.88 Q41324687698.91 Q43608312681.88 Q43855177782.87 Q44556843737.91 Q45748806138.91 Q46309744770.91 Q46311840365.87 Q47282368501.87 Q47312252080.87 Q49545476915.87 Q51241282684.87 Q52818999351.87 Q52821082840.91 Q53500367258.87 Q53519998161.87 Q56964988266.87 Q59322611797.87 Q59365683033.87 Q61975411717.91 Q62824840384.87 Q63037122486.87 Q6460837458.87  Q66715486460.87 Q67805910652.87 00000100200300=00>00E00M00U00]00g01301@01M01N01[01d01i02102602=02>02H02M02R02\02j02k03303403E03F03G03\03i03j04:04H04I04Z04[04e04j04k05005505605;05A05B05C05K05L05M05N05O05Z05e05f05g05h05i05j05k05l05m05n05o06006106@06K06Z06e07407?07N07Y07h08308B08M08\08g09609A09B09C09D09P09Q09R09\09]09n09o0:80:90:>0:U0:V0:W0:X0:Y0:n0;60;R0;W0;X0;]0;j0<>0<G0<U0<l0<m0<n0<o0=40=50=60=70=E0=F0=[0=o0>00>M0>Z0>[0>k0?;FFFS1P1n1N2B0FS1n3BIGS1P1n2LTS1P1n2B0S1P1n2B0S1P1n1N2B0S1P1n2q13Q45S1P1n3H8a3H8bS1P1n3H8a3H8bFS1P1n3H8b3H8aS1n5SMALLS1P1nS1P1n2ARS1n1NS1n3BIGFS1P1n1N2B0S1P1nS1P1nS1P1n1N2NZS1P1n2q02q12DBFS1P1n2GESS1P1n2q02q12DB2LTFFS1P1n2B02q02q12E03Q01S1P1n3H8b3H8aFS1P1n1N5SMALL2NZS1P1n2B05SMALLFS1P1n2q02q12DB2GEFS1P1n1N2B0S1P1nSS1P1nS1P1nFS1n1NS1n2N0FFS1P1n2B0FFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp1P1n2lo3LO0S2sp2lo3LO0S2sp1P1n2lo3LO0S2sp2lo3LO0S2sp1P1n2lo3LO0S2sp2lo3LO0S2sp1P1n2lo3LO0S2sp2lo3LO0S2sp1P1n2lo3LO0S2sp2lo3LO0S2sp1P1n2lo3LO0S2sp2lo3LO0S2sp1P1n2lo3LO0S2sp2lo3LO0S2sp1P1n2lo3LO0S2sp2lo3LO0FFFS1P1n2q13Q45FFS1P1n1N2NZFS1P1n2B02q02q12DBFS1P1n3H8bFS1P1nS1P1n1N2B02q02q13Q012DBFFFFS1P1n2B02q02q12E03Q01S1P1n2q0S2AL1P1n4IMG'2B02q02q12E12DBS1P1nFS1P1nS2AL1P1n4IMG'S2AL1P1n4IMG'2B03H8bS1P1n3H8bS1P1n2q02q12DBS1P1n1N2B02q02q13Q012DBFFFS1P1nFFFS2AL1P1n5ALWF'FS1P1n2B02q02q13Q452DBS1P1n2B02q02q12E12DBFS2AL1P1n4IMG'2B02q02q12E03Q01S2AL1P1n4IMG'FS2AL1P1n4IMG'2B0S2AL1P1n4IMG'2B0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma mic_chkP : ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))PP,$0.Pn,$0.Plo,$0.P,(22.$?.VAL,VCS,R4.R3.R2.)P,(:.(7.=R3.)(;.R3.(<.+2.+28.)))P,(23.R5.(18.(18.R5.R4.)+7.))P,P,(7.+1.R5.)(:.(24.VCS,(8.R7.(25.R7.+40.))+40.)(24.VCS,(8.(8.(18.R7.R6.)+1.)(25.(8.(18.R7.R6.)+1.)+40.))+40.))P,Pc,$0.P,A1.VCS,R1.(=.(2.&8.)Lb,(2.&8.)(>.$?.R;.(26.VAL,R3.)(10.(2.&8.)R1.(11.(2.&8.)))))P,(27.R9.)P,(21.$?.R:.R7.(1>.&40.R2:.))P,(;.+10007???7???.R8.)P,(7.R9.(8.(1>.&40.R2<.)+50.))P,(24.VCS,R:.(8.(1>.&40.R2=.)R:.))P,(20.$?.R>.)P,(6.(2.&40.)R1=.(17.&40.R>.))P,(6.(2.&40.)R29.(17.&40.R>.))(13.$?.VAL,VCS,(28.R31.R30.R2?.R2;.R29.R21.R20.R1>.R1<.R1;.R18.R13.R12.R10.R?.R>.R11.)(15.(16.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(17.&40.+5953<.)R12.(19.(2.&40.))R11.(1:.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < P /\ P + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    Ltac ripP P n lo SCS :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx P n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := P) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep;
      unfold micP_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. (* [comment removed for export] *) zstep. if_trueU. ripP P n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold micP_post; finish. }
    replace ((1 <=? n) && (n <=? 64))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
    if_falseU.
    destruct (HULL ltac:(lia)) as [HULL0 HULL1].
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m P n OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    (* [comment removed for export] *)
    qc_block11 P n E0 E1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold micP_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (P + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((P + n - 1) / 8) 2147450880) in RDk.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (P / 8) ((P + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply mic_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [left; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (P / 8) with ((P + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & a4' & ->)).
    (* [comment removed for export] *)
    zstep. zstep.
    if_cases Ks.
    2:{ ripP P n lo SCS. }
    unfold micP_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition micQ_post (sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Lms',$14.(=.(2.&40.)Lra,(2.&40.)(=.(2.&40.)Lt0,(2.&40.)(=.(2.&40.)Lt1,(2.&40.)(=.(2.&40.)Lt2,(2.&40.)(=.(2.&40.)La0,(2.&40.)(=.(2.&40.)La1,(2.&40.)(=.(2.&40.)La2,(2.&40.)(=.(2.&40.)La3,(2.&40.)(=.(2.&40.)La4,(2.&40.)(=.(2.&40.)La5,(2.&40.)(=.(2.&40.)La6,(2.&40.)(=.(2.&40.)La7,(2.&40.)(=.(2.&40.)Ls6,(2.&40.)(=.(2.&40.)Ls9,(2.&40.)(=.(2.&40.)Lt3,(2.&40.)(=.(2.&40.)Lt4,(2.&40.)(=.(2.&40.)Lt5,(2.&40.)(=.(2.&40.)Lt6,(2.&40.)(=.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(:.(6.$14.R14.(15.(16.R13.O11.O10.O?.R12.R11.R10.O>.O=.R?.R>.R=.R<.R;.R:.R9.R8.O<.O;.O:.O9.R7.O8.O7.R6.O6.O5.R5.R4.R3.R2.)O4.(17.&40.+595=0.)O3.(19.(2.&40.))R1.(1:.$?.)))(:.(1;.(10.(1<.$0.$0.)(1=.$0.$0.O2.(1>.&40.O11.))(11.(1<.$0.$0.)))O1.R1.)(:.(1?.$?.O1.R1.)(:.(20.$?.R1.)(21.$?.R1.O2.(1>.&40.O11.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@C17025492443.112C17025492443.87 L11447729190.143L11449284700.91 L11944109973.87 L14345069909.68 L19500905321.86 L19628431903.89 L20966712717.91 L24122754266.91 L24122936649.91 L24124928684.85 L24124928684.86 L24608617390.69 L24982526223.89 L25229963513.91 L25792253067.67 L27196467039.68 L2805262342.71  L28083348026.87 L28442596129.0  L29784464483.90 L29786564236.86 L29971684470.69 L31686803170.91 L3248729870.2   L3421674955.91  L34922678286.2  L36929494798.2  L36996769802.71 L37009347163.86 L38143997504.55 L38150352304.91 L39594679749.86 L45607281678.2  L46815385100.85 L46817748388.71 L47543971773.91 L49899794702.2  L51172192526.2  L52065394884.85 L52514161039.89 L53517158443.68 L53519158063.89 L61097676998.2  L61932014891.68 L64596837268.69 L65307978869.91 L66488557582.2  L7106453518.2   L9331589222.86  O14206727921.112O14206727921.87 O15547502833.112O15547502833.87 O17025492443.112O17025492443.87 O23485702385.112O23485702385.87 O32131581681.112O32131581681.87 O38504098033.112O38504098033.87 O4492316913.112 O4492316913.87  O48978854641.112O48978854641.87 O65485481713.112O65485481713.87 P3245129067.112 P3245129067.87  P34917767787.112P34917767787.87 P36941614443.112P36941614443.87 P45611546219.112P45611546219.87 P49904706411.112P49904706411.87 P51184575339.112P51184575339.87 P66501341803.112P66501341803.87 P7102853739.112 P7102853739.87  Q11345175648.86 Q19275945964.86 Q21797814763.86 Q23650890746.90 Q24488278781.86 Q24745328269.90 Q28218390483.90 Q28545998839.90 Q29427030349.86 Q31394395900.86 Q34268098539.86 Q34947676851.86 Q36722057835.86 Q3742509637.86  Q38148316102.86 Q39778974580.86 Q39942779359.86 Q41324687698.90 Q43608312681.87 Q43855177782.86 Q44556843737.90 Q45748806138.90 Q46309744770.90 Q46311840365.86 Q48043271576.90 Q48395817976.86 Q49545476915.86 Q51241282684.86 Q52818999351.86 Q52821082840.90 Q52937855287.86 Q53029148074.86 Q53519998161.86 Q56411855217.87 Q56964988266.86 Q59322611797.86 Q59365683033.86 Q60567301245.86 Q62824840384.86 Q63037122486.86 Q6460837458.86  Q65464757216.86 Q66715486460.86 Q67805910652.86 Q68542923397.86 Q8594361845.87  00000100200300;00<00C00M00W00c01001=01>01K01T01Y01j01o02602>02?02@02E02J02T02b02c03403503603>03F03N03c04004104;04K04Y04Z04[04e04j04k05005105605<05D05E05F05K05L05M05N05O05Z05e05f05g05h05i05j05k05l05m05n05o06006106@06K06Z06e07407?07N07Y07h08308B08M08\08g09609A09B09N09O09P09Q09b09k09l09m0:20:I0:J0:K0:L0:a0:i0;E0;F0;K0;X0;l0<50<C0<Z0<[0<\0<]0<b0<c0<d0<e0<f0=40=90=:0=O0=c0=d0>A0>N0>O0>P0>`0?00?10?;FFFS1Q1n2GEFS1n3BIGS1Q1n1N2B0S1Q1n1N2B0S1Q1n2q13Q45S1Q1n3H8a3H8bS1Q1n3H8a3H8bFS1Q1n3H8b3H8aS1n5SMALLS1Q1nS1Q1n2q02q12DB2GES1n1NS1n3BIGS1Q1n2B0FSS1Q1nS1Q1nS1Q1n1N2NZS1Q1n2q02q12DBFS1Q1n2q02q12DB2LTFFS1Q1n2B0S1Q1n2B0S1Q1n2ARS1Q1n2B02q02q12E03Q01S1Q1n3H8b3H8aFS1Q1n1N2B0S1Q1n1N5SMALL2NZS1Q1n2B05SMALLFFS1Q1n1N2B0S1Q1nSS1Q1nFS1n1NS1n2N0S1Q1n2LTFFS1Q1nFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp1Q1n2lo3LO0S2sp2lo3LO0S2sp1Q1n2lo3LO0S2sp2lo3LO0S2sp1Q1n2lo3LO0S2sp2lo3LO0S2sp1Q1n2lo3LO0S2sp2lo3LO0S2sp1Q1n2lo3LO0S2sp2lo3LO0S2sp1Q1n2lo3LO0S2sp2lo3LO0S2sp1Q1n2lo3LO0S2sp2lo3LO0S2sp1Q1n2lo3LO0S2sp2lo3LO0FS1Q1n2q13Q45FFFS1Q1n2B02q02q12DBS1Q1n3H8bFFS1Q1nS1Q1n1N2B02q02q13Q012DBFFFS1Q1n2B02q02q12E03Q01S1Q1n2q0S2AL1Q1n4IMG'2B02q02q12E12DBFS1Q1nS2AL1Q1n4IMG'S2AL1Q1n4IMG'2B03H8bS1Q1n3H8bS1Q1n2q02q12DBS1Q1n1N2B02q02q13Q012DBFFFS1Q1nFFFFS2AL1Q1n5ALWF'S1Q1nFS1Q1n2B02q02q13Q452DBS1Q1n2B02q02q12E12DBFS2AL1Q1n4IMG'2B02q02q12E03Q01S2AL1Q1n4IMG'FFS2AL1Q1n4IMG'2B0S2AL1Q1n4IMG'2B0FS1Q1n1N2NZ". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma mic_chkQ : ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))PQ,$0.Pn,$0.Plo,$0.P,(22.$?.VAL,VCS,R4.R3.R2.)P,(:.(7.=R3.)(;.R3.(<.+2.+28.)))P,(23.R5.(18.(18.R5.R4.)+7.))P,P,(7.+1.R5.)(:.(24.VCS,(8.R7.(25.R7.+40.))+40.)(24.VCS,(8.(8.(18.R7.R6.)+1.)(25.(8.(18.R7.R6.)+1.)+40.))+40.))P,Pc,$0.P,A1.VCS,R1.(=.(2.&8.)Lb,(2.&8.)(>.$?.R;.(26.VAL,R3.)(10.(2.&8.)R1.(11.(2.&8.)))))P,(27.R9.)P,(21.$?.R:.R7.(1>.&40.R2:.))P,(;.+10007???7???.R8.)P,(7.R9.(8.(1>.&40.R2<.)+50.))P,(24.VCS,R:.(8.(1>.&40.R2=.)R:.))P,(20.$?.R>.)P,(6.(2.&40.)R1?.(17.&40.R>.))P,(6.(2.&40.)R29.(17.&40.R>.))P,(6.(2.&40.)R1:.(17.&40.(18.R?.-41.)))(13.$?.VAL,VCS,(29.R32.R31.R30.R2<.R2;.R22.R21.R20.R1?.R1=.R1<.R1:.R19.R14.R13.R?.R12.)(15.(16.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(17.&40.+5958<.)R13.(19.(2.&40.))R12.(1:.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI -> -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < Q /\ Q + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    Ltac ripQ Q n lo SCS :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx Q n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := Q) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep;
      unfold micQ_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. (* [comment removed for export] *) zstep. if_trueU. ripQ Q n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold micQ_post; finish. }
    replace ((1 <=? n) && (n <=? 64))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
    if_falseU.
    destruct (HULL ltac:(lia)) as [HULL0 HULL1].
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m Q n OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    qc_block11 Q n E0 E1.
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold micQ_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (Q + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((Q + n - 1) / 8) 2147450880) in RDk.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (Q / 8) ((Q + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply mic_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [right; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (Q / 8) with ((Q + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & a4' & ->)).
    zstep. zstep.
    if_cases Ks.
    2:{ ripQ Q n lo SCS. }
    unfold micQ_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac shrd_now1 SHRD MU SCS name :=
    lazymatch type of MU with munch ?W _ ?mx =>
      assert (name : forall c, CS c -> exists b, bytes_at asegs mx (shadow_of AL c) [b])
        by (eapply (shrd_munch AL CS CSOK W); [ | exact MU | exact SHRD ];
            unfold w_client; apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil])
    end.

  Definition micpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (ps qs : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Lms',$14.(=.$0.Lr,$0.(=.(2.&40.)Lt0,(2.&40.)(=.(2.&40.)Lt1,(2.&40.)(=.(2.&40.)Lt2,(2.&40.)(=.(2.&40.)La1,(2.&40.)(=.(2.&40.)La2,(2.&40.)(=.(2.&40.)La3,(2.&40.)(=.(2.&40.)La4,(2.&40.)(=.(2.&40.)La5,(2.&40.)(=.(2.&40.)La6,(2.&40.)(=.(2.&40.)La7,(2.&40.)(=.(2.&40.)Lt3,(2.&40.)(=.(2.&40.)Lt4,(2.&40.)(=.(2.&40.)Lt5,(2.&40.)(=.(2.&40.)Lt6,(2.&40.)(=.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(:.(6.$14.R11.(15.(16.O16.O15.O14.O13.R?.R>.R=.O12.O11.(17.&40.R10.)R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(2:.O16.)O5.(19.(2.&40.))R1.(1:.$?.)))(:.(1;.(10.(1<.$0.$0.)(1=.$0.$0.O4.(1>.&40.O15.))(11.(1<.$0.$0.)))O1.R1.)(:.(1?.$?.O1.R1.)(:.(20.$?.R1.)(:.(2;.(6.$0.R10.=)(6.(2<.(2.&8.))O3.O2.))(:.(:.(7.-??.R10.)(7.R10.+??.))(21.$?.R1.O4.(1>.&40.O15.))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac mic_front P Q n lo sp SHRD MU SCS ST HULLP HULLQ :=
    (* [comment removed for export] *)
    carve_frame 48%nat ST;
    do 8 zstep;
    (* [comment removed for export] *)
    do 8 zstep;
    (* [comment removed for export] *)
    zstep; zstep; zstep; zstep;
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ lo _ |- _ => carve_frame 16%nat H end;
    do 13 zstep;
    lazymatch goal with FR16 : rw_cells _ _ (bv_unsigned sp + -64) _, H : stk _ _ lo _ |- _ => release_frame FR16 H (bv_unsigned sp + -48)%Z end;
    (* [comment removed for export] *)
    do 9 zstep;
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ lo _ |- _ => carve_frame 104%nat H; carve_frame 2088%nat H end;
    do 16 zstep;
    (* [comment removed for export] *)
    do 13 zstep;
    (* [comment removed for export] *)
    zstep; zstep; rewrite zb_lxor_ones by lia; if_falseU;
    (* [comment removed for export] *)
    let SHRD1 := fresh "SHRD1" in
    let SHRD2 := fresh "SHRD2" in
    shrd_now1 SHRD MU SCS SHRD1;
    lazymatch goal with OBJx : aobj _ _ _ ?mx P n |- _ (MS _ _ _ _ _ ?mx _) =>
      callxA_sp (bv_unsigned sp + -2240)
        (eapply mic_chkP with (P := P) (n := n) (lo := lo);
         rewrite ?(unsigned_lit (bv_unsigned sp + -2240)) by lia;
         first [ exact OBJx | exact HULLP | exact SHRD1 | split; assumption | eassumption
               | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
    end;
    clear SHRD1;
    (* [comment removed for export] *)
    zstep; zstep; rewrite zb_lxor_ones by lia; if_falseU;
    (* [comment removed for export] *)
    shrd_now1 SHRD MU SCS SHRD2;
    lazymatch goal with OBJx : aobj _ _ _ ?mx Q n |- _ (MS _ _ _ _ _ ?mx _) =>
      callxA_sp (bv_unsigned sp + -2240)
        (eapply mic_chkQ with (Q := Q) (n := n) (lo := lo);
         rewrite ?(unsigned_lit (bv_unsigned sp + -2240)) by lia;
         first [ exact OBJx | exact HULLQ | exact SHRD2 | split; assumption | eassumption
               | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
    end;
    clear SHRD2;
    (* [comment removed for export] *)
    zstep; zstep; zstep; zstep.

  (* [comment removed for export] *)
  Ltac mic_back lo sp :=
    (* [comment removed for export] *)
    do 26 zstep;
    lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -2240) _, H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -152)%Z end;
    lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -152) _, H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -48)%Z end;
    (* [comment removed for export] *)
    do 6 zstep;
    lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -48) _, H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06N0@C17025492443.116C17027589631.135L10704730584.135L10704730584.90 L11123517328.1  L11151000370.89 L11670997746.89 L11670997746.93 L11671095915.133L11741095640.133L11741095640.84 L11845421885.2  L12283411672.87 L12724448472.135L12724448472.90 L13082847747.90 L13612370320.1  L13945566013.2  L14892571425.0  L17751112592.1  L17842913240.135L17842913240.90 L19064786548.90 L19275232829.2  L19354909044.85 L1952314207.133 L19960529714.139L20228169497.67 L20469438006.111L20899370550.112L20899370551.94 L21263946840.135L21263946840.90 L21702772658.91 L2228046919.91  L24425513366.2  L24741311300.93 L2490130320.1   L25382082548.85 L25796462352.112L25796462353.94 L25867342416.1  L26087768692.90 L26810617703.133L26924648792.133L26924648792.85 L27575339581.2  L27909133984.136L28164510486.2  L29879403325.2  L30126571198.93 L30284306320.1  L30503973080.135L30503973080.90 L31101643124.90 L31180098100.112L31180098101.94 L31378308326.87 L31392867444.85 L32098570484.90 L32216200280.137L32958506430.132L33923427958.138L34806738575.133L34994544387.87 L35104026255.133L35265264016.1  L36423785504.90 L36605650392.135L36605650392.90 L36695631704.135L36695631704.90 L37009352592.133L37114660852.90 L37414286068.85 L37827447170.89 L37827660420.88 L38124170612.90 L38250533174.112L38250533175.94 L38927657760.137L41311429558.133L41373956902.91 L4173929907.135 L4173929907.90  L4268008459.1   L43055531689.85 L43442376564.84 L43507554877.2  L43654564952.133L43654564952.85 L43877851626.112L43877851627.94 L44135496692.90 L44279461264.1  L4516270424.135 L4516270424.90  L46229568912.1  L46815388615.133L46817616122.107L46817616122.111L47261106520.136L47433200395.1  L48429240188.89 L49137712701.2  L50156898420.90 L51721692860.135L51925114228.87 L52067390900.84 L52155331762.131L52677716797.2  L52843640797.2  L53142273605.2  L53436504664.135L53436504664.90 L54422382992.1  L55456222552.135L55456222552.90 L56184006388.90 L56494809917.2  L572478269.2    L58228050206.94 L58228050207.112L59362373472.135L59499841752.85 L60580974680.135L60580974680.90 L60698274187.93 L61684362301.2  L61891563670.2  L61931847947.133L61931946386.93 L61933814326.111L62194807668.90 L62554460978.139L62693820120.135L62693820120.90 L63593677629.2  L64788204432.1  L64969717103.131L65837833277.2  L66307532359.90 L67158371251.87 L68220404212.90 L68305792912.1  L68354046352.1  L7510805464.133 L7510805464.85  L7691419910.111 L8003688082.135 L8019544820.90  L9213084816.1   N21303764596.136N27801652866.136N44259866089.117N64040766665.117O11318304277.135O11320401457.116O14206727921.116O14208825045.135O15545405653.135O15547502833.116O17025492443.116O17027589631.135O23485702385.116O23487799509.135O29398866161.116O29400963285.135O30740199153.116O30742296277.135O31029914933.135O31032012049.116O32129484501.135O32131581681.116O38073090773.135O38075187953.116O38504098033.116O38506195157.135O4492316913.116 O4494414037.135 O48978854641.116O48980951765.135O65483384533.135O65485481713.116O66400803569.116O66402900693.135P11136886036.91 P11136886036.92 P11136886036.94 P11136886036.97 P11857680728.116P11859777916.135P13615778580.91 P13615778580.92 P13615778580.94 P13615778580.97 P13955981692.135P13958078808.116P17762908436.91 P17762908436.92 P17762908436.94 P17762908436.97 P19261006972.135P19263104088.116P2493537556.91  P2493537556.92  P2493537556.94  P2493537556.97  P25855545556.91 P25855545556.92 P25855545556.94 P25855545556.97 P27570296920.116P27572394108.135P29865316732.135P29867413848.116P30297150740.91 P30297150740.92 P30297150740.94 P30297150740.97 P35252419348.91 P35252419348.92 P35252419348.94 P35252419348.97 P43512727640.116P43514824828.135P44284442388.91 P44284442388.92 P44284442388.94 P44284442388.97 P46232977172.91 P46232977172.92 P46232977172.94 P46232977172.97 P49125452888.116P49127550076.135P52665334104.116P52667431292.135P52837148060.135P52839245240.116P54410586900.91 P54410586900.92 P54410586900.94 P54410586900.97 P56498680152.116P56500777340.135P584073560.116  P586170748.135  P61677485692.135P61679582808.116P63595450748.135P63597547864.116P64783223060.91 P64783223060.92 P64783223060.94 P64783223060.97 P65847594620.135P65849691736.116P68310248724.91 P68310248724.92 P68310248724.94 P68310248724.97 P68366891796.91 P68366891796.92 P68366891796.94 P68366891796.97 P9225930260.91  P9225930260.92  P9225930260.94  P9225930260.97  Q11739043422.93 Q13345394735.93 Q15457446739.91 Q1548373386.89  Q15643324129.87 Q15645781315.136Q15798398436.93 Q17695203997.89 Q18365925601.88 Q18376656032.93 Q18382986998.138Q19120365881.93 Q21325202062.93 Q21877548704.90 Q21877548707.93 Q21892398326.138Q22417345682.93 Q24385202550.138Q24387466016.93 Q24990120750.90 Q24992217868.88 Q25513505925.90 Q25513505925.91 Q25513505925.93 Q25513505925.96 Q25604052563.88 Q25604052563.89 Q25831247586.93 Q27582847683.93 Q27597684885.138Q29152429779.94 Q29501324949.138Q29503382723.93 Q29628353130.94 Q30402624502.138Q30412939680.93 Q31180098100.112Q31180098101.94 Q31258969621.138Q31269428291.90 Q31269428291.93 Q317029817.93   Q32655500769.88 Q32657827395.136Q33918256002.88 Q34065779714.93 Q36012250132.93 Q36423785504.90 Q36423785504.93 Q36438361718.138Q37821600610.90 Q37821600610.91 Q38248387216.116Q38250484404.135Q3830427394.88  Q3836357792.136 Q38929625846.138Q38931622048.93 Q39911317326.93 Q39937162656.136Q39939554818.88 Q40924557666.90 Q40926654784.88 Q41139582357.138Q41154490304.93 Q41154490307.90 Q41386762978.96 Q42451356320.93 Q42457878774.138Q42884747718.89 Q43877802600.135Q43879899724.116Q43928033258.91 Q44648843873.88 Q44654840259.136Q44948594038.138Q44959172384.93 Q4531421635.93  Q4546337685.138 Q47314197898.89 Q47520249092.93 Q48477108512.93 Q48479232886.138Q48727422869.138Q48729615811.93 Q49698585326.89 Q49698585326.90 Q49698585326.92 Q49698585326.95 Q50373998991.93 Q5057285269.138 Q5059614403.93  Q50764080396.88 Q50766177582.90 Q50851990851.93 Q50866444053.138Q50969982368.93 Q50984890358.138Q51220952259.136Q51235796833.88 Q52099073603.93 Q52105534485.138Q52877482670.93 Q53128511161.96 Q53355200917.138Q53365464003.93 Q53519968643.90 Q53519968643.93 Q53522065825.88 Q53522246311.89 Q54481423862.138Q54487881632.93 Q5677907779.93  Q5680030997.138 Q56995717152.93 Q57006242422.138Q59244144917.138Q59254666051.93 Q60498843766.138Q60513354272.93 Q62022695231.93 Q62629877019.88 Q62631974201.90 Q63320363541.138Q63331076163.93 Q64998166283.89 Q66522067074.88 Q66536583968.136Q66686485353.93 Q66971591087.90 Q66973688205.88 Q67140319936.89 Q67528989526.91 Q67528989526.92 Q67528989526.94 Q67528989526.97 Q705100644.90   Q707197766.88   Q7377275490.93  Q9024774830.93  Q9475007385.93  Q9693545246.93  Q9836715552.136 Q9843367298.87  00000100200<00F00G00N00c01801M01W01a01b01l02602@02J02K02L02M02N02X02b02l02m03703G03N04B04R04S04T04^04h04o05905@05J05K05U05g06906:06D06E06O06Y06Z06k07207307H07I07S07]07g08@08Y08c08m09709A0:70:H0:[0:e0;30;40;E0;O0;Y0;c0;m0<=0<G0<Q0<b0=30==0=G0=Q0=b0=c0>40>>0>H0>L0>]0>g0>h0?20?<0?I0?V0?`0?a0?k0@50@60@K0@`0A50A?0AC0AM0AN0AX0Ab0Al0Am0B40B50B60B70BA0BK0BL0BV0B`0Bj0Bk0Bl0C=0CN0CZ0Cd0Cn0D80DH0DI0DP0Db0E40EF0EP0EW0Ea0Ek0El0Em0Fa0Fb0Fl0G60G@0GA0GB0GL0GV0Gk0H70HA0HB0HU0Hh0I;0IN0IO0IP0IQ0IR0IS0IT0I_0Ij0Ik0Il0Im0In0Io0J00J10J20J30J40J50J60J70J80J90J:0J;0J<0J=0J>0J?0J@0Jg0KT0L:0MA0MR0Mc0NJ0O70O]0Pd0Q50QF0Qm0RZ0S@0TG0TX0Ti0UP0V=0Vc0Wj0XQ0Y>0Yd0Zk0[<0[M0[^0[o0\V0]C0]i0_00_W0`D0`j0b10bB0bS0c:0cg0dM0eT0f;0fh0gN0hU0hf0i70iH0iY0ij0j;0jb0kO0l50m<0mM0m^0mo0n@0nQ0nb0o30oD0ok10X11>12E12V12g13N14;14a15h16O17<17b18i19P1:=1:c1;j1<91<:1<G1<N1<[1<h1=71=81=E1=V1=g1>I1>P1>a1?21?C1?D1?U1?f1?m1@41@S1A81AV1BU1Bb1Bo1C01C=1CJ1CW1Cd1D11D>1DO1D`1E91ER1E_1El1F91F:1FG1FT1Fe1Ff1G51GF1GW1Gh1HK1I41I>1IH1IY1Ij1J;1JL1J[1Jl1K=1K>1K?1KL1KY1Kf1Le1M61MG1MH1MU1Mb1Mo1N<1NI1NZ1Nk1O81OE1OT1Oc1P41PE1PR1P_1Q61QM1Qd1R;1R<1RI1RV1Re1S41SA1SN1S_1T01T=1TJ1TW1Td1Tk1UO1U\1Ui1V91VI1VY1Vi1W:1WK1WX1We1X61XG1XT1Xa1Y21YC1YD1YE1YF1YS1Y`1Ya1Z21ZC1ZD1ZE1ZF1ZU1[81[a1\C1]F1]U1]d1^D1^S1^T1^[1^l1_=FFS2sp2ps2qsS2sp2ps2qsFS2ps2qsS1P1Q1n2ps2qs4LENP2B0S1P1Q1n2ps2qs4LENP2B0S1P1Q1n2ps2qs4LENP2B0S2sp2ps2qsS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFSFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFS2sp2ps2qsS1P1Q1n2ps2qs2B0S2ps2qsS2sp1P1Q1n2lo2ps2qs4LENP3ARP3ARQ3LO03SPL5DISJP5DISJQS1P1Q1n2ps2qs2B0FFS2sp2ps2qsS2sp2ps2qsS2ps2qsS2sp2ps2qsS2sp2loS2sp2ps2qsFS2sp2ps2qsS1P1Q1n2ps2qs1N2B0S1P1Q1n2ps2qs1N2B0FS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsFS2sp2lo2ps2qs3SPLS2sp2loFS1P1Q1n2ps2qs4LENP2B0FS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qs3LO03SPL3SPRS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp1P1Q1n2lo2ps2qs4LENP4LENQ3ARP3ARQ3LO03SPL5DISJQ2B0S2sp2lo2ps2qs3SPLS1n2ps2qs4LENP4LENQS2sp2ps2qsS1n2ps2qs4LENPFS2sp2lo2ps2qs3SPLS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS1P1Q1n2ps2qs2B0S2sp2ps2qsS2sp2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2ps2qsS2lo2ps2qsS2lo2ps2qsS2sp2lo2ps2qs3SPLFS2sp2lo2ps2qs3SPLS2sp2ps2qsS2sp2ps2qsS2spS2sp2lo2ps2qs3SPLS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsFS1P1Q1n2ps2qs4LENP2B0S1P1Q1n2ps2qs4LENP2B0S1P1Q1n2ps2qs4LENP2B0S2sp2ps2qsS2spS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFS2ps2qsFFFS2sp2ps2qsS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2ps2qs1r2HrS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS1P1Q1n2ps2qs2B0FS2sp2loS1P1Q1n2ps2qs1N2B0S1P1Q1n2ps2qs1N2B0S1P1Q1n2ps2qs1N2B0S2sp2ps2qsS2ps2qsS2sp2ps2qsS2sp2ps2qsFFS2sp1P1Q1n2lo2ps2qs4LENP3ARP3ARQ3LO03SPL5DISJP5DISJQFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFS2sp2ps2qsS2sp2ps2qsS1P1Q1n2ps2qs4LENP2B0S2ps2qs1r2HrS2sp2ps2qsFS2sp2lo2ps2qs3x361CS2sp2lo2ps2qs3x361CS2sp2lo2ps2qs3x171CS2sp2lo2ps2qs3x171CFFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFFFFFFFFFFFS2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2AL2ps2qs4IMG'FS2sp2ps2qs2HBS2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2AL2ps2qs4IMG'FS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp1n2lo2ps2qs3SPL2HB5Ha_st5Hl_stS2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2ps2qsS2ps2qsS2ra2sp2lo2ps2qs2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2ps2qs2HBS2sp2ps2qs2HBFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs2HBS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs2HBS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLFS2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2ra2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3SPL2HB5Ha_st5Hl_st2s12s2S2lo2ps2qsS2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s10S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs2HBS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2AL2ps2qs4IMG'S2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs3SPR2HB5Ha_stS2sp2ps2qs3SPR2HB5Ha_stS2sp2ps2qs3SPR2HB5Ha_stS2sp2ps2qs3SPR2HB5Ha_stFS2sp2lo2ps2qsS2sp2lo2ps2qsS2AL2ps2qs4IMG'S2AL2ps2qs4IMG'S2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2ps2qsS2sp3s112lo2ps2qs3SPL2HB5Ha_st5Hl_stS2sp2lo2ps2qsS2sp2lo2ps2qsS2AL2ps2qs5ALWF'S2AL2ps2qs5ALWF'S2AL2ps2qs5ALWF'S2AL2ps2qs5ALWF'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFFFS2sp2lo2ps2qsS2sp2lo2ps2qsFS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFFFS2AL2ps2qs4IMG'S2ra2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2AL2ps2qs4IMG'S2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_stS2AL2ps2qs4IMG'FS2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Theorem memcmp_icpt_spec : ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))PP,$0.PQ,$0.Pn,$0.Plo,$0.Pps,(2<.(2.&8.))Pqs,(2<.(2.&8.))P,(>.$?.R7.R6.R2.)P,(>.$?.R8.R6.R2.)P,(6.$0.(9.(2=.(2.&8.)R4.))R6.)P,(6.$0.(9.(2=.(2.&8.)R4.))R7.)P,(22.$?.VAL,VCS,R;.R:.R8.)P,(22.$?.VAL,VCS,R<.R:.R9.)P,(;.R:.(<.+2.+28.))P,(23.R=.(18.(18.R=.R;.)+7.))P,(23.R=.(18.(18.R=.R<.)+7.))P,P,(7.+1.R=.)(:.(24.VCS,(8.R10.(25.R10.+40.))+40.)(24.VCS,(8.(8.(18.R10.R>.)+1.)(25.(8.(18.R10.R>.)+1.)+40.))+40.))P,P,(7.+1.R>.)(:.(24.VCS,(8.R10.(25.R10.+40.))+40.)(24.VCS,(8.(8.(18.R10.R?.)+1.)(25.(8.(18.R10.R?.)+1.)+40.))+40.))P,Pc,$0.P,A1.VCS,R1.(=.(2.&8.)Lb,(2.&8.)(>.$?.R15.(26.VAL,R3.)(10.(2.&8.)R1.(11.(2.&8.)))))P,(2>.R13.)P,(21.$?.R14.R10.(1>.&40.R34.))P,(;.+10007???7???.R11.)P,(7.R12.(8.(1>.&40.R36.)+910.))P,(24.VCS,R13.(8.(1>.&40.R37.)R13.))P,(5.(7.(18.R17.R15.)R14.)(7.(1>.&40.R38.)R17.))P,(5.(7.(18.R17.R16.)R15.)(7.(1>.&40.R39.)R17.))P,(20.$?.R1:.)P,(6.(2.&40.)R33.(17.&40.R1:.))P,(6.(2.&40.)R33.(17.&40.R1:.))P,(6.(2.&40.)R33.(17.&40.R1:.))(13.$?.VAL,VCS,(2?.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.R1:.R19.R18.R1>.)(15.(16.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(17.&40.+59=54.)R1?.(19.(2.&40.))R1>.(1:.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros until qs. intros HP HQ LENP LENQ OBJP OBJQ N ARP ARQ HULLP HULLQ SHRD MC ST LO0 SPL SCS DISJP DISJQ MI -> -> ->.
    al_facts. unfold app_range in ARP, ARQ.
    assert (B0 : 0 < P /\ 0 <= n /\ P + n + 7 <= HME /\ 0 < Q /\ Q + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof MC as MC'. destruct MC as [MC1 MC2 MC3 MC4 MC5 MC6 RC]. pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    pose proof (conj HP HQ) as KEEP. clear HP HQ.
    mic_front P Q n lo sp SHRD MU SCS ST HULLP HULLQ.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      destruct KEEP as [HP HQ];
      pose proof (bytes_at_transport asegs _ m mx P ps HP MU ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HP';
      pose proof (bytes_at_transport asegs _ m mx Q qs HQ MU ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HQ'
    end.
    eapply evtA_cut.
    { eapply (A_memcmp_evtA AL CS IMG) with (xs := ps) (ys := qs); rewrite ?unsigned_lit by lia;
        first [ exact HP' | exact HQ' | lia | exact (aobj_crange _ _ _ _ _ _ OBJP) | exact (aobj_crange _ _ _ _ _ _ OBJQ) ]. }
    cbn beta. intros ms' PO. hnf in PO. ddestruct PO as (a0' & a1' & a2' & a3' & a4' & r & -> & -> & Hr & Hiff).
    replace (ret_pc (Z_to_bv 64 0x595e0)) with (Z_to_bv 64 0x595e0) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    clear HP' HQ'.
    mic_back lo sp.
    unfold micpt_post; finish; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0750@C17025492443.116C17025492443.152C17027589631.135K19064441528.152K3389551664.152 L10704730584.144L10704730584.90 L11066428804.132L11123517328.1  L11649888584.144L11670997746.89 L11670997746.93 L11741095640.142L11741095640.84 L11845421885.2  L12283411672.87 L12724448472.144L12724448472.90 L13082847747.90 L13612370320.1  L13945566013.2  L14892571425.0  L1626348570.144 L17751112592.1  L17842913240.144L17842913240.90 L19064786548.90 L19069164249.4  L19275232829.2  L19354909044.85 L19960529714.148L20228169497.67 L20469438006.111L20895356589.132L20899370550.112L20899370551.94 L21263946840.144L21263946840.90 L21394982131.132L2228046919.91  L24425513366.2  L24741311300.93 L2490130320.1   L25382082548.85 L25796462352.112L25796462353.94 L25867342416.1  L26087768692.90 L26924648792.142L26924648792.85 L27227874881.132L27575339581.2  L27911231108.145L28164510486.2  L29879403325.2  L30126571198.93 L30284306320.1  L30503973080.144L30503973080.90 L31101643124.90 L31180098100.112L31180098101.94 L31184407215.132L31378308326.87 L31392867444.85 L32098570484.90 L32214103164.146L32958506430.133L33923037060.147L3401589841.4   L34994544387.87 L35265264016.1  L36423785504.90 L36605650392.144L36605650392.90 L36695631704.144L36695631704.90 L37114660852.90 L37414286068.85 L37827447170.89 L37827660420.88 L38124170612.90 L38238294445.132L38250533174.112L38250533175.94 L38929754884.146L41373956902.91 L4173929907.144 L4173929907.90  L4268008459.1   L43055531689.85 L43442376564.84 L43507554877.2  L43654564952.142L43654564952.85 L43877851626.112L43877851627.94 L43882127729.132L44135496692.90 L44279461264.1  L4516270424.144 L4516270424.90  L45210756786.89 L46229568912.1  L46817616122.107L46817616122.111L47259009404.145L47433200395.1  L48429240188.89 L49137712701.2  L50156898420.90 L51723789976.144L51925114228.87 L52067390900.84 L52677716797.2  L52843640797.2  L53142273605.2  L53436504664.144L53436504664.90 L54422382992.1  L54801566514.91 L55456222552.144L55456222552.90 L56184006388.90 L56494809917.2  L572478269.2    L58228050206.94 L58228050207.112L59499841752.85 L60580974680.144L60580974680.90 L60698274187.93 L61684362301.2  L61891563670.2  L61931946386.93 L61933814326.111L62194807668.90 L62693820120.144L62693820120.90 L63284397746.131L63593677629.2  L64788204432.1  L64971865047.132L65837833277.2  L66307532359.90 L67158371251.87 L68220404212.90 L68305792912.1  L68354046352.1  L7510805464.142 L7510805464.85  L7691419910.111 L8019544820.90  L9213084816.1   L9783175090.148 N21303764596.136N27801652866.136N44259866089.117N56865552736.153N6347814582.153 N64040766665.117O11318304277.135O11320401457.116O11320401457.152O14206727921.116O14206727921.152O14208825045.135O15545405653.135O15547502833.116O15547502833.152O17025492443.116O17025492443.152O17027589631.135O23485702385.116O23485702385.152O23487799509.135O29398866161.116O29398866161.152O29400963285.135O29478932113.152O30318897943.152O30740199153.116O30740199153.152O30742296277.135O31029914933.135O31032012049.116O31032012049.152O32129484501.135O32131581681.116O32131581681.152O38073090773.135O38075187953.116O38075187953.152O38504098033.116O38504098033.152O38506195157.135O4492316913.116 O4492316913.152 O4494414037.135 O48978854641.116O48978854641.152O48980951765.135O65483384533.135O65485481713.116O65485481713.152O66400803569.116O66400803569.152O66402900693.135P11136886036.91 P11136886036.92 P11136886036.94 P11136886036.97 P11857680728.116P11857680728.152P11859777916.135P13615778580.91 P13615778580.92 P13615778580.94 P13615778580.97 P13955981692.135P13958078808.116P13958078808.152P17762908436.91 P17762908436.92 P17762908436.94 P17762908436.97 P19261006972.135P19263104088.116P19263104088.152P2493537556.91  P2493537556.92  P2493537556.94  P2493537556.97  P25855545556.91 P25855545556.92 P25855545556.94 P25855545556.97 P27570296920.116P27570296920.152P27572394108.135P29865316732.135P29867413848.116P29867413848.152P30297150740.91 P30297150740.92 P30297150740.94 P30297150740.97 P35252419348.91 P35252419348.92 P35252419348.94 P35252419348.97 P43512727640.116P43512727640.152P43514824828.135P44284442388.91 P44284442388.92 P44284442388.94 P44284442388.97 P46232977172.91 P46232977172.92 P46232977172.94 P46232977172.97 P49125452888.116P49125452888.152P49127550076.135P52665334104.116P52665334104.152P52667431292.135P52837148060.135P52839245240.116P52839245240.152P54410586900.91 P54410586900.92 P54410586900.94 P54410586900.97 P56498680152.116P56498680152.152P56500777340.135P584073560.116  P584073560.152  P586170748.135  P61677485692.135P61679582808.116P61679582808.152P63595450748.135P63597547864.116P63597547864.152P64783223060.91 P64783223060.92 P64783223060.94 P64783223060.97 P65847594620.135P65849691736.116P65849691736.152P68310248724.91 P68310248724.92 P68310248724.94 P68310248724.97 P68366891796.91 P68366891796.92 P68366891796.94 P68366891796.97 P9225930260.91  P9225930260.92  P9225930260.94  P9225930260.97  Q11739043422.93 Q13345394735.93 Q15457446739.91 Q15643324129.87 Q15647878503.145Q15798398436.93 Q18365925601.88 Q18376656032.93 Q18382587652.147Q19120365881.93 Q19269719366.89 Q19902106507.89 Q20748626186.89 Q21325202062.93 Q21877548704.90 Q21877548707.93 Q21892523268.147Q22035341632.89 Q22417345682.93 Q24385597572.147Q24387466016.93 Q24990120750.90 Q24992217868.88 Q25513505925.90 Q25513505925.91 Q25513505925.93 Q25513505925.96 Q25604052563.88 Q25604052563.89 Q25831247586.93 Q27582847683.93 Q27597822311.147Q29152429779.94 Q29501450087.147Q29503382723.93 Q29628353130.94 Q30402748932.147Q30412939680.93 Q31180098100.112Q31180098101.94 Q31184407215.132Q31258583015.147Q31269428291.90 Q31269428291.93 Q317029817.93   Q32655500769.88 Q32659924583.145Q33918256002.88 Q34065779714.93 Q36012250132.93 Q36423785504.90 Q36423785504.93 Q36438237060.147Q37821600610.90 Q37821600610.91 Q38248387216.116Q38248387216.152Q38250484404.135Q3830427394.88  Q3834260612.145 Q38929754884.147Q38931622048.93 Q39911317326.93 Q39935065476.145Q39939554818.88 Q40924557666.90 Q40926654784.88 Q41139448935.147Q41154490304.93 Q41154490307.90 Q41318099229.89 Q41386762978.96 Q42451356320.93 Q42457483524.147Q43877802600.135Q43879899724.116Q43879899724.152Q43928033258.91 Q44648843873.88 Q44652743143.145Q44948456580.147Q44959172384.93 Q4531421635.93  Q4546462311.147 Q46644429066.89 Q47520249092.93 Q48477108512.93 Q48478845572.147Q48727813735.147Q48729615811.93 Q49698585326.89 Q49698585326.90 Q49698585326.92 Q49698585326.95 Q50373998991.93 Q5057680743.147 Q5059614403.93  Q50764080396.88 Q50766177582.90 Q50851990851.93 Q50866835175.147Q50969982368.93 Q50984498692.147Q51223049447.145Q51235796833.88 Q52099073603.93 Q52105659879.147Q52877482670.93 Q53128511161.96 Q53354813543.147Q53365464003.93 Q53519968643.90 Q53519968643.93 Q53522065825.88 Q53522246311.89 Q54481818628.147Q54487881632.93 Q5677907779.93  Q5679643879.147 Q56995717152.93 Q57005843332.147Q59244540135.147Q59254666051.93 Q60498968964.147Q60513354272.93 Q62022695231.93 Q62629877019.88 Q62631974201.90 Q63320755175.147Q63331076163.93 Q66522067074.88 Q66534486788.145Q66686485353.93 Q66971591087.90 Q66973688205.88 Q67528989526.91 Q67528989526.92 Q67528989526.94 Q67528989526.97 Q705100644.90   Q707197766.88   Q7377275490.93  Q9024774830.93  Q9475007385.93  Q9693545246.93  Q9838812676.145 Q9843367298.87  00000100200300X01B01L01V01g01h02702L02a02k03503603@03J03T03^03_03`03a04004104;04E04O04P04Q04[04b05V05f05g05h05i06306=06V06`06g07107207<07N07`07a07k08508?08X08Y08j09109209G09H09R09\09f0:?0:X0;10;;0;E0;O0;Y0<O0<`0<a0<k0<l0==0=G0=Q0=[0=e0=o0>90>J0>[0>e0>o0?90?C0?T0?e0?o0@90@=0@N0@X0@Y0@c0@m0A:0AG0AT0A^0A_0Ai0B30B:0B;0BP0Be0Bo0C30C=0C>0CH0CR0C\0C]0C^0C_0C`0Cj0D40D50D<0DF0DP0DZ0D[0D\0Dm0E>0EH0ER0E\0El0Em0F40FF0FX0Fb0Fl0G60G=0G>0G?0H30H40H>0HH0HR0HS0HT0H^0Hh0I=0IG0IH0IO0Ib0J50JH0J[0Jn0KA0KB0KC0KD0KE0KF0KG0KH0KI0KJ0KU0K`0Kk0Kl0Km0Kn0Ko0L00L10L20L30L40L50L60L70L80L90L:0L;0L<0L=0L>0L?0L@0LA0LB0LC0LD0LE0LF0LG0LH0LI0LJ0LK0LL0LM0LN0M50Mb0NH0OO0O`0P10PB0Pi0QV0R<0SC0ST0Se0T60T]0UJ0V00W70WH0WY0Wj0XQ0Y>0Yd0Zk0[R0\?0\e0]l0^=0^N0^_0_00_A0_R0`90`f0aL0bS0c:0cg0dM0eT0ee0f60fG0fn0g[0hA0iH0io0j\0kB0lI0lZ0lk0m<0mM0m^0mo0n@0nQ0nb0oI10610\11c12412E12V12g13813I13Z13k14<14M14^14o15V16C16i18018A18R18c19J1:71:]1;d1<K1=81=^1>e1?L1@91@_1Af1B51B61BC1BP1B]1Bl1C91CJ1C[1D=1D>1D?1DN1DU1Df1E71EH1EW1EX1Ei1F:1FA1FH1Fg1GL1Gj1Hi1I61IC1ID1IQ1I^1Ik1J81JE1JR1Jc1K41KM1Kf1L?1LL1LY1Lf1Lg1M41MA1MR1MS1Mb1N31ND1NU1O81Oa1Ok1P51P?1PP1Pa1Q21QC1QR1Qc1R41R51R61RC1RP1R]1R^1S]1Sn1T?1TL1TY1Tf1U31U@1UM1U^1Uo1V<1VI1VP1V_1W01WA1WN1W[1X21XI1X`1Y71Y81YE1YR1Ya1Z01Z=1ZJ1Z[1Zl1[91[F1[S1[`1[g1\K1\X1\e1]51]E1]U1]e1^61^G1^T1^a1_21_C1_P1_]1_n1`?1`@1`A1`B1`O1`\1`m1a>1a?1a@1aA1ad1bM1bo1d21dA1dP1e01e?1e@1eG1eX1eiFFFS2sp1P1Q1n2lo2ps2qs4LENP3LO05DISJP2B0S2sp1P1Q1n2lo2ps2qs4LENP4LENQ3LO05DISJQ2B0S2sp2ps2qsS2sp2ps2qsS2sp2lo2ps2qs3SPLFS2ps2qs3x363PC0S1P1Q1n2ps2qs4LENP2B0S1P1Q1n2ps2qs4LENP2B0S2sp2ps2qsS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFSS2ps2qs3x363PC0FS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFS2sp2ps2qsS2ps2qsS2sp1P1Q1n2lo2ps2qs4LENP3ARP3ARQ3LO03SPL5DISJP5DISJQS1P1Q1n2ps2qs2B0FFFS2sp2ps2qsS2sp2ps2qsS2sp1P1Q1n2lo2ps2qs5DISJQS2sp2ps2qsS2sp2loS2sp2ps2qsFS2sp2ps2qsS1P1Q1n2ps2qs1N2B0S1P1Q1n2ps2qs1N2B0FS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp1P1Q1n2lo2ps2qs5DISJPFS2sp2lo2ps2qs3SPLS2sp2loFS1P1Q1n2ps2qs4LENP2B0FS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qs3LO03SPL3SPRS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp1P1Q1n2lo2ps2qs4LENP4LENQ3ARP3ARQ3LO03SPL5DISJQ2B0S2sp2lo2ps2qs3SPLFS2sp2ps2qsFS2sp2lo2ps2qs3SPLS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2ps2qsS2lo2ps2qsS2lo2ps2qsS2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2ps2qsS2sp2ps2qsS2spS2sp2lo2ps2qs3SPLS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2ps2qsFS1P1Q1n2ps2qs4LENP2B0S1P1Q1n2ps2qs4LENP2B0S2sp2ps2qsS2spS2sp2ps2qsFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFFFS2sp2ps2qsS2sp2ps2qsFS2ps2qsS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS1P1Q1n2ps2qs2B0FS2sp2loS1P1Q1n2ps2qs1N2B0S1P1Q1n2ps2qs1N2B0S2sp2ps2qsS2sp2ps2qsS2sp2ps2qsS2ps2qsFFS2sp1P1Q1n2lo2ps2qs4LENP3ARP3ARQ3LO03SPL5DISJP5DISJQFS2sp2ps2qsS2sp2ps2qsS2sp2ps2qsFFS2sp2ps2qsS2sp2ps2qsS1P1Q1n2ps2qs4LENP2B0S2sp2ps2qsFS2ps2qsS2sp2lo2ps2qs3x361CS2sp2lo2ps2qs3x361CS2sp2lo2ps2qs3x171CS2sp2lo2ps2qs3x521CS2sp2lo2ps2qs3x521CS2sp2lo2ps2qs3x171CFFFFFFFFFS2sp2lo3SPLS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2sp2lo2ps2qs3LO0S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2ra2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3LO03SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2AL2ps2qs4IMG'FS2sp2ps2qs2HBS2sp2lo2ps2qsS2sp2lo2ps2qsS2AL2ps2qs4IMG'S2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp1n2lo2ps2qs3SPL2HB5Ha_st5Hl_stFFS2AL2ps2qs4IMG'S2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2AL2ps2qs4IMG'FS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2ps2qsS2ps2qsS2ra2sp2lo2ps2qs2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2sp2ps2qs2HBS2sp2ps2qs2HBFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs2HBS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs2HBS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qs3LO03SPL3SPRS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLFS2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2ra2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3SPL2HB5Ha_st5Hl_st2s12s2S2lo2ps2qsS2lo2ps2qsS2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsFS2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s10S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs2HBS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2ps2qsS2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2ps2qs3SPR2HB5Ha_stS2sp2ps2qs3SPR2HB5Ha_stS2sp2ps2qs3SPR2HB5Ha_stS2sp2ps2qs3SPR2HB5Ha_stFS2sp2lo2ps2qsS2sp2lo2ps2qsS2AL2ps2qs4IMG'S2AL2ps2qs4IMG'S2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qsS2ps2qsS2sp3s112lo2ps2qs3SPL2HB5Ha_st5Hl_stS2sp2lo2ps2qsS2sp2lo2ps2qsS2AL2ps2qs5ALWF'S2AL2ps2qs5ALWF'S2AL2ps2qs5ALWF'S2AL2ps2qs5ALWF'S2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFFFS2sp2lo2ps2qsS2sp2lo2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPLFFFS2ra2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_stS2sp2s02lo2ps2qs3SPL2HB5Ha_st5Hl_st2s12s2S2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_st1nS2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_st1n1Q1P2s32s42s52s62s72s82s93s103s11S2AL2ps2qs4IMG'S2AL2ps2qs4IMG'S2sp2lo2ps2qs3SPL2HB5Ha_st5Hl_stS2AL2ps2qs4IMG'FS2ps2qsS2sp2lo2ps2qs3SPLS2sp2lo2ps2qs3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Theorem bcmp_icpt_spec : ltac2:(CDefT.buildp (gd_tbl_A_bcmp ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))PP,$0.PQ,$0.Pn,$0.Plo,$0.Pps,(2<.(2.&8.))Pqs,(2<.(2.&8.))P,(>.$?.R7.R6.R2.)P,(>.$?.R8.R6.R2.)P,(6.$0.(9.(2=.(2.&8.)R4.))R6.)P,(6.$0.(9.(2=.(2.&8.)R4.))R7.)P,(22.$?.VAL,VCS,R;.R:.R8.)P,(22.$?.VAL,VCS,R<.R:.R9.)P,(;.R:.(<.+2.+28.))P,(23.R=.(18.(18.R=.R;.)+7.))P,(23.R=.(18.(18.R=.R<.)+7.))P,P,(7.+1.R=.)(:.(24.VCS,(8.R10.(25.R10.+40.))+40.)(24.VCS,(8.(8.(18.R10.R>.)+1.)(25.(8.(18.R10.R>.)+1.)+40.))+40.))P,P,(7.+1.R>.)(:.(24.VCS,(8.R10.(25.R10.+40.))+40.)(24.VCS,(8.(8.(18.R10.R?.)+1.)(25.(8.(18.R10.R?.)+1.)+40.))+40.))P,Pc,$0.P,A1.VCS,R1.(=.(2.&8.)Lb,(2.&8.)(>.$?.R15.(26.VAL,R3.)(10.(2.&8.)R1.(11.(2.&8.)))))P,(2>.R13.)P,(21.$?.R14.R10.(1>.&40.R34.))P,(;.+10007???7???.R11.)P,(7.R12.(8.(1>.&40.R36.)+11=0.))P,(24.VCS,R13.(8.(1>.&40.R37.)R13.))P,(5.(7.(18.R17.R15.)R14.)(7.(1>.&40.R38.)R17.))P,(5.(7.(18.R17.R16.)R15.)(7.(1>.&40.R39.)R17.))P,(20.$?.R1:.)P,(6.(2.&40.)R33.(17.&40.R1:.))P,(6.(2.&40.)R33.(17.&40.R1:.))P,(6.(2.&40.)R33.(17.&40.R1:.))(13.$?.VAL,VCS,(2?.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.R1:.R19.R18.R1>.)(15.(16.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(17.&40.+58704.)R1?.(19.(2.&40.))R1>.(1:.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros until qs. intros HP HQ LENP LENQ OBJP OBJQ N ARP ARQ HULLP HULLQ SHRD MC ST LO0 SPL SCS DISJP DISJQ MI -> -> ->.
    al_facts. unfold app_range in ARP, ARQ.
    assert (B0 : 0 < P /\ 0 <= n /\ P + n + 7 <= HME /\ 0 < Q /\ Q + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof MC as MC'. destruct MC as [MC1 MC2 MC3 MC4 MC5 MC6 RC]. pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    pose proof (conj HP HQ) as KEEP. clear HP HQ.
    (* [comment removed for export] *)
    zstep.
    mic_front P Q n lo sp SHRD MU SCS ST HULLP HULLQ.
    (* [comment removed for export] *)
    zstep. zstep.
    shrd_now1 SHRD MU SCS SH.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      destruct KEEP as [HP HQ];
      pose proof (bytes_at_transport asegs _ m mx P ps HP MU ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HP';
      pose proof (bytes_at_transport asegs _ m mx Q qs HQ MU ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HQ';
      clear HP HQ
    end.
    callxA_sp (bv_unsigned sp + -2240)
      (eapply memcmp_icpt_spec with (P := P) (Q := Q) (n := n) (lo := lo) (ps := ps) (qs := qs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -2240)) by lia;
       first [ exact HP' | exact HQ' | exact LENP | exact LENQ | exact OBJP | exact OBJQ | exact HULLP | exact HULLQ | exact SH
             | eassumption | split; first [assumption | split; assumption]
             | reflexivity | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ]).
    clear SH HP' HQ'.
    mic_back lo sp.
    unfold micpt_post; finish; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

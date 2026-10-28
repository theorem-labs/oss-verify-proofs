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
Ltac2 gd_tbl_A_imemcpy () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.B.A_rip.rip_consts"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.ichkS_post"; "Walk.ichkD_post"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amem_consts"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amem_apart"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amemcpy_post"].


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
  Ltac qc_block X n E0 E1 :=
    do 10 zstep;
    rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
    replace (X + n + -1) with (X + n - 1) by lia;
    rewrite !Z.mod_small by lia;
    rewrite !land_m8 by lia; rewrite !hull_sh by lia;
    rewrite E0, E1.

  Definition ichkS_post (sp gp tp s0 s4 s5 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_imemcpy ()) "Lms',$0.(1.(2.&40.)Lra,(2.&40.)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Ls1,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Ls2,(2.&40.)(1.(2.&40.)Ls3,(2.&40.)(1.(2.&40.)Ls7,(2.&40.)(1.(2.&40.)Ls8,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R14.(6.(7.R13.O10.O?.O>.R12.R11.R10.O=.R?.(8.&40.O5.)(8.&40.O4.)(8.&40.O3.)R>.R=.R<.R;.R:.R9.R8.O<.O;.(8.&40.(9.O3.-41.))R7.R6.O:.O9.O8.R5.R4.R3.R2.)O7.(8.&40.+68;:4.)O6.(:.(2.&40.))R1.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.O2.(12.&40.O10.))(13.(?.$10.$10.)))O1.R1.)(4.(14.$<.O1.R1.)(4.(15.$<.R1.)(16.$<.R1.O2.(12.&40.O10.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@C17025492443.113C17025492443.88 L11447729190.144L11944109973.88 L13226205188.72 L13230398037.87 L14345069909.69 L18705684095.87 L1918331350.56  L19322770858.87 L19628431903.90 L20966712717.92 L24122754266.92 L24122936649.92 L24124928684.86 L24124928684.87 L24608617390.70 L24982526223.90 L25792253067.68 L27196467039.69 L28083348026.88 L29784464483.91 L29786564236.87 L29971684470.70 L31686803170.92 L3248729870.2   L3421674955.92  L34922678286.2  L36929494798.2  L38150352304.92 L39594679749.87 L41302442785.0  L41312602363.92 L45607281678.2  L46817748388.72 L47543971773.92 L49899794702.2  L51172192526.2  L52065394884.86 L52514161039.90 L53517158443.69 L53519158063.90 L5549769202.92  L61097676998.2  L61932014891.69 L64055233047.92 L64240928084.86 L64596837268.70 L66488557582.2  L7106453518.2   L82129492.72    O14206727921.113O14206727921.88 O15547502833.113O15547502833.88 O17025492443.113O17025492443.88 O23485702385.113O23485702385.88 O32131581681.113O32131581681.88 O38504098033.113O38504098033.88 O4492316913.113 O4492316913.88  O48978854641.113O48978854641.88 O65485481713.113O65485481713.88 P3245129067.113 P3245129067.88  P34917767787.113P34917767787.88 P36941614443.113P36941614443.88 P45611546219.113P45611546219.88 P49904706411.113P49904706411.88 P51184575339.113P51184575339.88 P66501341803.113P66501341803.88 P7102853739.113 P7102853739.88  Q11819106457.88 Q12384979828.87 Q17356333121.87 Q19275945964.87 Q20040127854.87 Q20109487353.87 Q21797814763.87 Q23650890746.91 Q24745328269.91 Q28218390483.91 Q29427030349.87 Q31394395900.87 Q31762069934.91 Q32231604980.87 Q33251509847.87 Q34268098539.87 Q34355500059.88 Q34947676851.87 Q35212026327.87 Q36722057835.87 Q3742509637.87  Q38148316102.87 Q39778974580.87 Q39942779359.87 Q41324687698.91 Q43608312681.88 Q43855177782.87 Q44556843737.91 Q44682733963.91 Q45748806138.91 Q45896845414.87 Q46309744770.91 Q46311840365.87 Q49545476915.87 Q51241282684.87 Q52818999351.87 Q52821082840.91 Q53519998161.87 Q56964988266.87 Q59322611797.87 Q59365683033.87 Q62824840384.87 Q63037122486.87 Q6460837458.87  Q66715486460.87 Q67805910652.87 00000100200300400>00H00O00[00e00l01801F01U01d01e02402=02D02I02P02Q02X02_02k03;03<03O03P03Q03h04704804K04L04^04n04o05005<05C05D05K05U05V05[05e06106706806906C06D06E06F06G06R06]06^06_06`06a06b06c06d06e06f06g06h06i07:07E07V07a08208=08N08Y08j09509F09Q09b09m0:>0:I0:U0:V0:W0:e0:f0:g0:h0:i0;<0;G0;H0;O0;P0;Q0;R0;k0<20<30<40<50<60<M0<W0=50=60==0=L0=b0=c0=n0=o0>?0>X0>Y0>`0>a0>b0?20?30?J0?`0@?0@N0@O0@a0A3FFFFS3SRC1n2B0S3SRC1n2B0S1n3BIGS3SRC1n1N2B0S3SRC1n2ARS3SRC1nS3SRC1n1N2B0S3SRC1n2q13Q45S3SRC1n3H8a3H8bS3SRC1n3H8a3H8bFS3SRC1n3H8a3H8bS1n5SMALLS3SRC1nS1n1NS1n3BIGFS3SRC1nS3SRC1nS3SRC1n1N2NZS3SRC1n2q02q12DBFS3SRC1n2q02q12DB2LTFFS3SRC1n2B02q02q12E03Q01S3SRC1n3H8a3H8bSS3SRC1n2q02q12DB2GEFS3SRC1n1N5SMALL2NZS3SRC1n2B05SMALLFFS3SRC1n1N2B0S3SRC1nSS3SRC1nS3SRC1n2GEFS1n1NS3SRC1n2LTS3SRC1n1N2B0S1n2N0FFS3SRC1n2B0FFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S3SRC1n1N2NZFFS3SRC1n2q13Q45FFFFS3SRC1n2B02q02q12DBS3SRC1n3H8bFS3SRC1nFFFS3SRC1n1N2B02q02q13Q012DBS3SRC1nFFFFS3SRC1n2B02q02q12E03Q01S3SRC1n2q0S2AL3SRC1n4IMG'2B02q02q12E12DBFS3SRC1nS2AL3SRC1n4IMG'S2AL3SRC1n4IMG'2B03H8bFS3SRC1n3H8bFS3SRC1n2q02q12DBS3SRC1n1N2B02q02q13Q012DBFS3SRC1nFFS2AL3SRC1n5ALWF'FS3SRC1n2B02q02q13Q452DBS3SRC1n2B02q02q12E12DBS2AL3SRC1n4IMG'2B02q02q12E03Q01S2AL3SRC1n4IMG'FS2AL3SRC1n4IMG'2B0S2AL3SRC1n4IMG'2B0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma imemcpy_chkS : ltac2:(CDefT.buildp (gd_tbl_A_imemcpy ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PDST,$10.PSRC,$10.Pn,$10.Plo,$10.P,(18.$<.VAL,VCS,R5.R3.R2.)P,(4.(19.=R3.)(1:.R3.(1;.+2.+28.)))P,(1<.R5.(9.(9.R5.R4.)+7.))P,P,(19.+1.R5.)(4.(1=.VCS,(1>.R7.(1?.R7.+40.))+40.)(1=.VCS,(1>.(1>.(9.R7.R6.)+1.)(1?.(1>.(9.R7.R6.)+1.)+40.))+40.))P,Pc,$10.P,A1.VCS,R1.(1.(2.&8.)Lb,(2.&8.)(20.$<.R<.(21.VAL,R3.)(>.(2.&8.)R1.(13.(2.&8.)))))P,(22.R:.)P,(16.$<.R;.R7.(12.&40.R2;.))P,(1:.+10007???7???.R8.)P,(19.R9.(1>.(12.&40.R2=.)+50.))P,(1=.VCS,R:.(1>.(12.&40.R2>.)R:.))P,(15.$<.R?.)P,(4.(19.=R?.)(1:.R?.(1;.+2.+40.)))P,(5.(2.&40.)R29.(8.&40.R10.))P,(5.(2.&40.)R29.(8.&40.R10.))P,(5.(2.&40.)R29.(8.&40.R10.))P,(5.(2.&40.)R23.(8.&40.(9.R12.R11.)))(23.$<.VAL,VCS,(24.R35.R34.R33.R2?.R23.R22.R1>.R1=.R1<.R17.R16.R14.R13.R12.R11.R15.)(6.(7.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(8.&40.+68;60.)R16.(:.(2.&40.))R15.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI DB0 -> -> -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < SRC /\ SRC + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    Ltac iripS SRC n lo SCS :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := SRC) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep;
      unfold ichkS_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. (* [comment removed for export] *) zstep. if_trueU. iripS SRC n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold ichkS_post; finish. }
    replace ((1 <=? n) && (n <=? 64))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
    if_falseU.
    destruct (HULL ltac:(lia)) as [HULL0 HULL1].
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m SRC n OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    (* [comment removed for export] *)
    qc_block SRC n E0 E1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold ichkS_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (SRC + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((SRC + n - 1) / 8) 2147450880) in RDk.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (SRC / 8) ((SRC + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply (amemcpy_orloop AL IMG ALWF CS CSOK) with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [do 3 right; left; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (SRC / 8) with ((SRC + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a5' & a6' & ->)).
    (* [comment removed for export] *)
    zstep. zstep.
    if_cases Ks.
    2:{ iripS SRC n lo SCS. }
    unfold ichkS_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition ichkD_post (sp gp tp s0 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_imemcpy ()) "Lms',$0.(1.(2.&40.)Lra,(2.&40.)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Ls1,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Ls2,(2.&40.)(1.(2.&40.)Ls3,(2.&40.)(1.(2.&40.)Ls4,(2.&40.)(1.(2.&40.)Ls6,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R14.(6.(7.R13.O11.O10.O?.R12.R11.R10.O>.R?.(8.&40.O5.)(8.&40.O4.)(8.&40.O3.)R>.R=.R<.R;.R:.R9.R8.R7.O=.R6.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(8.&40.+68;><.)O6.(:.(2.&40.))R1.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.O2.(12.&40.O11.))(13.(?.$10.$10.)))O1.R1.)(4.(14.$<.O1.R1.)(4.(15.$<.R1.)(16.$<.R1.O2.(12.&40.O11.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0280@C17025492443.112C17025492443.87 L11447729190.143L11944109973.87 L14345069909.68 L16029456145.71 L16033656128.86 L19628431903.89 L20966712717.91 L23189051853.55 L2394494565.91  L24122754266.91 L24122936649.91 L24124928684.85 L24124928684.86 L24608617390.69 L24982526223.89 L25792253067.67 L27050710447.71 L27196467039.68 L28083348026.87 L29784464483.90 L29786564236.86 L29971684470.69 L31686803170.91 L31723725750.67 L3241391265.0   L3248729870.2   L3421674955.91  L34922678286.2  L35600352231.67 L35692323376.91 L36929494798.2  L38150352304.91 L39594679749.86 L41794548952.86 L45607281678.2  L46817748388.71 L47543971773.91 L49899794702.2  L51172192526.2  L52065394884.85 L52514161039.89 L53517158443.68 L53519158063.89 L61097676998.2  L61402522944.85 L61402946443.66 L61402946443.67 L61931751947.67 L61932014891.68 L63477229558.86 L6351988974.91  L64596837268.69 L66488557582.2  L7106453518.2   O14206727921.112O14206727921.87 O15547502833.112O15547502833.87 O17025492443.112O17025492443.87 O23485702385.112O23485702385.87 O32131581681.112O32131581681.87 O38504098033.112O38504098033.87 O4492316913.112 O4492316913.87  O48978854641.112O48978854641.87 O65485481713.112O65485481713.87 P3245129067.112 P3245129067.87  P34917767787.112P34917767787.87 P36941614443.112P36941614443.87 P45611546219.112P45611546219.87 P49904706411.112P49904706411.87 P51184575339.112P51184575339.87 P66501341803.112P66501341803.87 P7102853739.112 P7102853739.87  Q10652825868.86 Q12854075564.86 Q19275945964.86 Q21797814763.86 Q23650890746.90 Q24745328269.90 Q25930949378.86 Q28218390483.90 Q29427030349.86 Q31394395900.86 Q34268098539.86 Q34947676851.86 Q36722057835.86 Q3742509637.86  Q37735318614.86 Q38148316102.86 Q39778974580.86 Q39942779359.86 Q41324687698.90 Q43608312681.87 Q43855177782.86 Q44556843737.90 Q45129161346.86 Q45748806138.90 Q46309744770.90 Q46311840365.86 Q49545476915.86 Q49598061100.86 Q51241282684.86 Q52818999351.86 Q52821082840.90 Q53519998161.86 Q54929902563.90 Q56964988266.86 Q58952702441.86 Q59322611797.86 Q59365683033.86 Q62824840384.86 Q63037122486.86 Q63979701653.90 Q6460837458.86  Q66715486460.86 Q6693426778.87  Q67304791703.87 Q67805910652.86 Q67834060547.86 00000100200300400;00E00O00[00i01301=01L01[01\01k02402;02@02J02Q02R02Y02`02l03<03F03G03H03[03\03h04204304J04Y04`04a05305C05D05E05Q05X05Y05`05a05m06906E06J06O06[06n07407507607707807907:07E07P07Q07R07S07T07U07V07W07X07Y07Z07[07\07m08808I08T08e09009A09L09]09h0:90:D0:U0:`0;10;<0;=0;>0;L0;M0;N0;a0;b0;m0;n0<50<N0<O0<P0<Q0<R0<i0=30=Q0=R0=Y0=h0>>0>?0>J0>Z0?30?40?50?<0?=0?>0?N0?O0?P0?Q0?h0@>0@]0@l0@m0@n0A@0AG0AS0Ae0AfFFFFS1n3BIGS3DST1n2B0S3DST1n2B0S3DST1n1N2B0S3DST1n2q13Q45S3DST1n2ARS3DST1n2GES3DST1n3H8a3H8bS3DST1n3H8a3H8bFS3DST1n3H8a3H8bS1n5SMALLS3DST1nS1n1NS3DST1n2B0S1n3BIGFS3DST1nS3DST1nS3DST1n1N2NZS3DST1n2q02q12DBS3DST1n2B0SFS3DST1n2q02q12DB2LTFS3DST1n1N2B0S3DST1n2LTFS3DST1n2B02q02q12E03Q01S3DST1n3H8a3H8bS3DST1nFS3DST1n1N5SMALL2NZS3DST1n2B05SMALLFFS3DST1n1N2B0S3DST1nSS3DST1nFS3DST1n1N2B0S3DST1n1N2B0S3DST1n1N2B0S1n1NS1n1NS3DST1n1N2B0S3DST1n2q02q12DB2GES1n2N0FFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0FFS3DST1n2q13Q45FFS3DST1n2B02q02q12DBFS3DST1n3H8bFS3DST1nS3DST1n1N2B02q02q13Q012DBFFFFS3DST1n2B02q02q12E03Q01S3DST1n2q0S2AL3DST1n4IMG'2B02q02q12E12DBFS3DST1nS2AL3DST1n4IMG'S2AL3DST1n4IMG'2B03H8bFS3DST1n3H8bS3DST1n2q02q12DBS3DST1n1N2B02q02q13Q012DBFFS3DST1nFFS2AL3DST1n5ALWF'FFFS3DST1n2B02q02q13Q452DBS3DST1n2B02q02q12E12DBS2AL3DST1n4IMG'2B02q02q12E03Q01S2AL3DST1n4IMG'FFS2AL3DST1n4IMG'2B0S3DST1nS3DST1n1N2NZS2AL3DST1n4IMG'2B0F". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma imemcpy_chkD : ltac2:(CDefT.buildp (gd_tbl_A_imemcpy ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PDST,$10.PSRC,$10.Pn,$10.Plo,$10.P,(18.$<.VAL,VCS,R5.R4.R2.)P,(4.(19.=R3.)(1:.R3.(1;.+2.+28.)))P,(1<.R6.(9.(9.R6.R4.)+7.))P,P,(19.+1.R5.)(4.(1=.VCS,(1>.R8.(1?.R8.+40.))+40.)(1=.VCS,(1>.(1>.(9.R8.R6.)+1.)(1?.(1>.(9.R8.R6.)+1.)+40.))+40.))P,Pc,$10.P,A1.VCS,R1.(1.(2.&8.)Lb,(2.&8.)(20.$<.R<.(21.VAL,R3.)(>.(2.&8.)R1.(13.(2.&8.)))))P,(22.R:.)P,(16.$<.R;.R7.(12.&40.R2;.))P,(1:.+10007???7???.R8.)P,(19.R9.(1>.(12.&40.R2=.)+50.))P,(1=.VCS,R:.(1>.(12.&40.R2>.)R:.))P,(15.$<.R?.)P,(4.(19.=R>.)(1:.R>.(1;.+2.+40.)))P,(5.(2.&40.)R29.(8.&40.R10.))P,(5.(2.&40.)R29.(8.&40.R10.))P,(5.(2.&40.)R29.(8.&40.R10.))P,(5.(2.&40.)R22.(8.&40.(9.R13.R11.)))P,(5.(2.&40.)R21.(8.&40.(9.R12.-41.)))(23.$<.VAL,VCS,(25.R36.R35.R34.R30.R23.R21.R20.R1?.R1>.R1=.R18.R17.R15.R14.R13.R12.R16.)(6.(7.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(8.&40.+68;:4.)R17.(:.(2.&40.))R16.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI SB0 -> -> -> -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < DST /\ DST + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    Ltac iripD DST n lo SCS :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := DST) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep;
      unfold ichkD_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. rewrite zb_lxor_ones by lia. if_falseU.
    zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. (* [comment removed for export] *) zstep. if_trueU. iripD DST n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold ichkD_post; finish. }
    replace ((1 <=? n) && (n <=? 64))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
    if_falseU.
    destruct (HULL ltac:(lia)) as [HULL0 HULL1].
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m DST n OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    qc_block DST n E0 E1.
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold ichkD_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (DST + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((DST + n - 1) / 8) 2147450880) in RDk.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (DST / 8) ((DST + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply (amemcpy_orloop AL IMG ALWF CS CSOK) with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [do 4 right; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (DST / 8) with ((DST + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a5' & a6' & ->)).
    zstep. zstep.
    if_cases Ks.
    2:{ iripD DST n lo SCS. }
    unfold ichkD_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac shrd_now SHRD MU SCS OBJD name :=
    lazymatch type of MU with munch ?W _ ?mx =>
      assert (name : forall c, CS c -> exists b, bytes_at asegs mx (shadow_of AL c) [b])
        by (eapply (shrd_munch AL CS CSOK W); [ | exact MU | exact SHRD ];
            unfold w_client; apply Forall_cons;
            [ cbn [fst snd]; lazymatch goal with |- crange _ _ (?a + ?k - _) => replace (a + k - a) with k by lia end;
              eapply aobj_crange; exact OBJD
            | apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil] ])
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0590@C17025492443.119C17027589631.138C29675049067.153K21979204025.153K47064714985.152K58434789865.152K61309466857.152K65658691719.153L11123517328.1  L11255914340.96 L13136158964.98 L13225815175.134L14218488609.0  L14826010361.134L15302269400.142L15302269400.88 L16029064082.134L17517655171.92 L17751112592.1  L19006798410.96 L20146841363.2  L2025501661.3   L20652354682.98 L20808779268.98 L21990708291.2  L22015551912.3  L22446743512.142L22446743512.88 L23267971501.73 L2423253472.134 L24383500448.148L24631371325.2  L25214214772.88 L25653881957.94 L25796462353.115L25796462354.96 L28563140627.2  L28860711850.98 L30284306320.1  L31225147636.88 L31227231805.2  L31944270486.2  L33818746643.2  L34128174314.3  L34609294877.96 L34609294878.115L34705680216.142L34705680216.88 L35265264016.1  L36119512893.2  L36897755907.88 L36914643987.2  L37246946676.87 L38250533172.96 L38250533175.115L3949578456.142 L3949578456.87  L40294402896.1  L40374333670.92 L40691620147.2  L41010467417.134L41843875160.142L41843875160.88 L42823025544.134L43055353660.90 L43616922521.4  L43877851624.96 L43877851627.115L44154175243.1  L45800883475.2  L45802451773.2  L46229568912.1  L46635263293.2  L46638324410.4  L47075365651.2  L48080000820.96 L48080000823.115L4831066756.149 L49220693398.134L49283344500.88 L49625125661.2  L50169871760.1  L51454941784.142L51454941784.88 L51952712129.4  L5343886661.2   L54207053188.97 L54243326995.2  L54422382992.1  L55050231357.2  L55310518004.88 L55356110389.115L55356110390.96 L55470097981.2  L56117591786.3  L5699067096.142 L5699067096.88  L57818804596.88 L58119466785.95 L58130246816.114L58423753747.2  L58591023192.142L58591023192.88 L59492225212.147L59878299197.2  L60290246322.135L61270427352.148L61320439059.2  L61321319284.88 L61390376978.96 L61398538917.97 L61398912846.98 L61400521381.97 L61935960466.96 L63529291102.98 L63829069812.88 L63975535526.134L64243071665.97 L64244674394.98 L64245054129.97 L64253079557.115L64253079558.88 L64253079558.96 L64788204432.1  L65655075046.4  L6610646974.97  L67275561872.1  L67280348888.142L67280348888.88 L67351568884.88 L68354046352.1  L7632799155.142 L7632799155.88  L7837352765.2   L8830339091.2   L9700656445.2   L9963177110.2   N13467909276.120N33291805818.120N54639299529.139N65749140201.139O14206727921.119O14208825045.138O15545405653.138O15547502833.119O17025492443.119O17027589631.138O23485702385.119O23487799509.138O28909731028.153O28953822661.138O28955919841.119O29675049067.153O30179188619.152O30286673803.152O32129484501.138O32131581681.119O3521469857.153 O35907574667.152O38504098033.119O38506195157.138O42849031057.119O42851128245.138O43116495243.152O4352777611.152 O4492316913.119 O4494414037.138 O45584088819.119O45586185943.138O48635945867.152O48978854641.119O48980951765.138O50651377905.119O50653475029.138O52051324628.153O52201094539.152O54335600011.152O55436697483.152O62532530571.152O65483384533.138O65485481713.119O66103434849.152O66254176497.119O66256273621.138O7921967435.152 P11136886036.98 P11136886036.99 P17762908436.98 P17762908436.99 P20140522217.152P2020832220.98  P2020832220.99  P21979204025.153P22027872681.98 P22027872681.99 P24642319484.138P24644416600.119P28568546793.152P30297150740.98 P30297150740.99 P31231224920.119P31233322108.138P33813332713.152P34135146768.153P35252419348.98 P35252419348.99 P36105295228.138P36107392344.119P36925037033.152P40289946068.98 P40289946068.99 P40697808073.152P43604540408.119P43606637532.138P45791156457.152P45814833496.119P45816930684.138P46232977172.98 P46232977172.99 P46625147103.152P46628255612.138P46630352728.119P49611030876.138P49613128056.119P50173804308.98 P50173804308.99 P51948005792.119P51950102916.138P54249710057.152P54410586900.98 P54410586900.99 P55059729532.138P55061826648.119P55474492504.119P55476589692.138P56110474000.153P59891074136.119P59893171324.138P64783223060.98 P64783223060.99 P67262191892.98 P67262191892.99 P68366891796.98 P68366891796.99 P7848300924.138 P7850398040.119 P8841319913.152 P9711605628.138 P9713702744.119 Q13482121755.95 Q15643324129.94 Q15647878503.149Q17530203490.97 Q17530203490.98 Q17974635083.95 Q18361895783.149Q18363828454.95 Q2186089982.134 Q21877548677.95 Q21892523268.149Q24385597572.149Q24387465989.95 Q24394897947.95 Q25513505925.97 Q25513505925.98 Q27582847718.95 Q27597822311.149Q27905103109.95 Q27911231108.149Q30402748932.149Q30412939653.95 Q31258583015.149Q31269428326.95 Q32653403622.95 Q32659924583.149Q33251554080.95 Q33913700356.149Q33916158853.95 Q35419777341.153Q36330714342.153Q36423785477.95 Q36438237060.149Q36722022172.95 Q38248387216.119Q38250484404.138Q3832524549.95  Q3834260612.149 Q39935065476.149Q39941651973.95 Q41139448935.149Q41154490342.95 Q43855338817.95 Q43877802600.138Q43879899724.119Q44650941030.95 Q44652743143.149Q46025024389.134Q49598033755.95 Q49698585326.96 Q49698585326.97 Q51000317356.95 Q51223049447.149Q51233699686.95 Q51241048331.95 Q5300226131.95  Q5300226131.96  Q5318114788.134 Q53519968678.95 Q53532715523.134Q54126458602.96 Q55356110389.115Q55356110390.96 Q57916578385.95 Q58215755193.134Q59244540135.149Q59254666086.95 Q59830194919.149Q59841040742.95 Q62283281657.98 Q62283281657.99 Q64191759790.134Q64536302640.95 Q66524164229.95 Q66534486788.149Q67806143243.95 Q8528270766.134 Q8892514873.98  Q9838812676.149 Q9843367298.94  00000100200300400]01F02302j02k03?03R03f03g05505?05I05]05n05o06^06_06`07U07h07i07j08408>09N09b0:30:40:>0:H0:^0;40;50;b0;c0;m0;n0<50<60<70<H0<Y0<c0<m0<n0<o0=90=:0=D0=N0=X0=b0=l0=m0>70>80>L0>V0>`0>n0??0?@0?M0?Z0?^0?_0?`0?a0?b0?c0?d0?e0?f0@70@J0@T0@U0@V0@`0@j0@k0@l0B;0B<0B=0B>0BH0Ba0C:0C;0C<0CF0CP0CZ0Cg0D40D50D?0DI0DS0DT0D[0De0Df0E00E_0F80Fg0GV0Gl0I?0II0I]0JL0K=0KX0LG0M60Me0Mf0Mg0NU0NV0N`0Nj0O40O50O?0OI0OJ0OK0OL0OS0Of0P90PL0P_0P`0Pa0Pb0Pc0Pn0Q90Q:0Q;0Q<0Q=0Q>0Q?0Q@0QA0QB0QC0QD0QE0QF0QG0QH0QI0QJ0QK0QL0QM0QN0QO0QP0QQ0QR0QS0QT0QU0QV0QW0QX0QY0QZ0Q[0Q\0Q]0Q^0Q_0RF0SE0Sl0Tk0UT0VH0WT0WU0XI0YU0Yf0Z70Z`0[G0\F0\W0\h0]Q0]n0^U0_T0_e0`60`_0aF0bE0bn0cL0cj0dS0dd0e50e\0f[0g40gE0gV0gg0h80h_0i^0j<0jZ0kC0kj0li0m:0mK0m\0mm0nJ0n[0nl0oS10R11912812_13^13o14@14i15:15K15R15_15l16O17G17H17U17b17c18418E18V18g19619U1:L1:Y1:f1;71;H1;Y1;j1<71<D1<Q1<^1<_1=01=A1=N1=Y1=j1>;1><1>F1>P1>a1?21?C1?T1?a1?n1@=1@J1@W1@d1A11A21A31AJ1Aa1Ab1Ao1B<1BC1BP1B]1Bl1C<1CL1CY1D21DK1DZ1D[1Dh1E51EB1EO1F81G91G@1GA1GR1Gc1H21HA1Hd1I51IFFFFFS3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP43AP22sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss4LENS3SEP2B02sp2lo3SPL5DISJD5DISJS3LO0FS3DST3SRC1n2ds2ss2B0S3DST3SRC1n2ds2ss1lS3DST3SRC1n2ds2ss2B0SS3DST3SRC1n2ds2ss3SEP3ARD3ARS3AP13AP23AP33AP43AP52B02sp2lo3SPL5DISJD5DISJS3LO0S2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss2B0S2sp2lo2ds2ss3SPLFS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSFFS3DST3SRC1n2ds2ss2B01l4LEND2sp2lo3LO03SPL5DISJS5DISJDS3DST3SRC1n2ds2ss1lFFS2sp2ds2ssS2sp2ds2ssS2sp3DST3SRC1n2lo2ds2ss4LEND3SEP3ARD3ARS3AP13AP23AP33AP43AP53LO03SPL5DISJD5DISJSS3DST3SRC1n2ds2ss2B0S2sp2lo2ds2ss3SPLFS2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss1N2B0S3DST3SRC1n2ds2ss1N2B0FS3DST3SRC1n2ds2ss4LEND2B02sp2lo3LO03SPL5DISJSFS2sp2ds2ssFS2sp2loFFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2ds2ssS2sp2ds2ssFFS2sp2ds2ssFS2sp2ds2ssS2lo2ds2ssS2lo2ds2ssS2sp2ds2ssS2sp2ds2ssFS2sp2ds2ssFS3DST3SRC1n2ds2ss2B0S2sp2ds2ssS2sp2ds2ssS1n2ds2ss4LENDS2sp2lo2ds2ss3SPLFS2sp2lo2ds2ssS2sp2lo2ds2ssS2spFFFFFFFFS2sp2lo2ds2ss3SPLS1n2ds2ss4LEND4LENSS2sp2ds2ssFFS2sp2ds2ssS2sp2ds2ssFFS3DST3SRC1n2ds2ss4LEND3ARD3ARS3AP13AP23AP33AP43AP52NE2sp2lo3SPL5DISJD5DISJS3LO0FFFS2sp2ds2ssS2sp2lo2ds2ss3LO03SPL3SPRS2sp2lo2ds2ss3LO03SPL3SPRFFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssS3DST1n2ds2ssS3DST1n2ds2ssFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssFS2ds2ssS2sp2ds2ssFS2sp2ds2ssS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B0S3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss1N2B0S3DST3SRC1n2ds2ss3SEP3ARD3ARS3AP13AP23AP33AP43AP52B02NE1l2sp2lo3SPL5DISJD5DISJS3LO0S2sp2ds2ssS3DST3SRC1n2ds2ss2B0S3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss2B01l4LEND2sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B01ES3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSFFS3DST3SRC2ds2ss1E2sp1n2lo4LEND3SPL5DISJD5DISJSFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssFS2sp2ds2ssS2sp2ds2ssFFFS2sp2loS2sp2lo2ds2ss3x181CS2sp2lo2ds2ss3x181CS2sp2lo2ds2ss3x371CS2sp2lo2ds2ss3x371CFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2ra2sp3DST1n2lo2ds2ss4LEND3SPL5DISJD2HB5Ha_st5Hl_stS2sp2s03DST1n2lo2ds2ss4LEND3SPL5DISJD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8FS2ra2sp3SRC1n2lo2ds2ss4LENS3SPL5DISJS2HB5Ha_st5Hl_stS2sp2s03SRC1n2lo2ds2ss4LENS3SPL5DISJS2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2sp3DST1n2lo2ds2ss3SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2sp3DST1n2lo2ds2ss4LEND5DISJDS2sp3DST1n2lo2ds2ss4LEND5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp3DST1n2lo2ds2ss5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp3SRC1n2lo2ds2ss4LENS5DISJSS2sp3SRC1n2lo2ds2ss4LENS5DISJSS3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp3DST1n2lo2ds2ss3SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2ra2sp2lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2AL2ds2ss4IMG'S2ra2sp2lo2ds2ss2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS3DST1n2ds2ssS3DST2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLFS2lo2ds2ssS2lo2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2AL2ds2ss4IMG'S2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssFFS2sp2ds2ss3SPR2HB5Ha_stS2sp2ds2ss3SPR2HB5Ha_stFS2sp2lo2ds2ssS2sp2lo2ds2ssS2ds2ssS2sp2ds2ss2HBS2sp2ds2ss2HBS2AL2ds2ss4IMG'S2AL2ds2ss5ALWF'S2AL2ds2ss5ALWF'S2sp2ds2ss2HBS2sp2lo2ds2ss3LO03SPL3SPRS2sp2lo2ds2ss3LO03SPL3SPRS2AL2ds2ss4IMG'FS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2ra2sp3DST1n2lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2s03DST1n2lo2ds2ss3SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2ds2ssFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2AL2ds2ss4IMG'S2AL2ds2ss4IMG'S2sp2s82lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Theorem imemcpy_spec : ltac2:(CDefT.buildp (gd_tbl_A_imemcpy ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PDST,$10.PSRC,$10.Pn,$10.Plo,$10.Pds,(26.(2.&8.))Pss,(26.(2.&8.))P,(27.$<.R7.R6.R2.)P,(20.$<.R8.R6.R2.)P,(5.$10.(28.(29.(2.&8.)R4.))R6.)P,(5.$10.(28.(29.(2.&8.)R4.))R7.)P,(18.$<.VAL,VCS,R;.R:.R8.)P,(18.$<.VAL,VCS,R<.R:.R9.)P,(2:.(5.$10.R:.=)(2:.(19.(9.R<.R:.)R;.)(19.(9.R;.R:.)R<.)))P,(1:.R;.(1;.+2.+28.))P,(1<.R>.(9.(9.R>.R<.)+7.))P,(1<.R>.(9.(9.R>.R=.)+7.))P,P,(19.+1.R>.)(4.(1=.VCS,(1>.R11.(1?.R11.+40.))+40.)(1=.VCS,(1>.(1>.(9.R11.R?.)+1.)(1?.(1>.(9.R11.R?.)+1.)+40.))+40.))P,P,(19.+1.R?.)(4.(1=.VCS,(1>.R11.(1?.R11.+40.))+40.)(1=.VCS,(1>.(1>.(9.R11.R10.)+1.)(1?.(1>.(9.R11.R10.)+1.)+40.))+40.))P,Pc,$10.P,A1.VCS,R1.(1.(2.&8.)Lb,(2.&8.)(20.$<.R16.(21.VAL,R3.)(>.(2.&8.)R1.(13.(2.&8.)))))P,(2;.R14.)P,(2<.R14.R12.)P,(16.$<.R16.R12.(12.&40.R36.))P,(1:.+10007???7???.R13.)P,(19.R14.(1>.(12.&40.R38.)+8<0.))P,(1=.VCS,R15.(1>.(12.&40.R39.)R15.))P,(2:.(19.(9.R19.R17.)R16.)(19.(12.&40.R3:.)R19.))P,(2:.(19.(9.R19.R18.)R17.)(19.(12.&40.R3;.)R19.))P,(15.$<.R1<.)P,(5.(2.&40.)R35.(8.&40.R1<.))P,(5.(2.&40.)R35.(8.&40.R1<.))P,(5.(2.&40.)R35.(8.&40.R1<.))(23.$<.VAL,VCS,(2=.R41.R40.R3?.R3>.R3:.R39.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R22.R21.R1?.R1>.R1=.R1<.R1:.R20.)(6.(7.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R22.(8.&40.+68:?8.)R21.(:.(2.&40.))R20.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until ss. (intros ARR SRCB LEND LENS OBJD OBJS SEP N ARD ARS HULLD HULLS SHRD AC dd_H; ddestruct dd_H as (AP1 & AP2 & AP3 & AP4 & AP5); intros ST LO0 SPL SCS DISJD DISJS MI -> -> ->). al_facts. unfold app_range in ARD, ARS.
    assert (B0 : 0 < DST /\ 0 <= n /\ DST + n + 7 <= HME /\ 0 < SRC /\ SRC + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(DST, DST + n); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof AC as AC'. destruct AC as [AC1 AC2 AC3 AC4 RC]. pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    pose proof (rw_cells_of_u8arr asegs m DST ds ARR) as DSTC. clear ARR.
    (* [comment removed for export] *)
    destruct DISJD as [DISJD|DISJD]; destruct DISJS as [DISJS|DISJS];
      (* [comment removed for export] *)
      carve_frame 80%nat ST; rename FR into FRS; carve_frame 2080%nat ST;
      (* [comment removed for export] *)
      do 17 zstep;
      (* [comment removed for export] *)
      shrd_now SHRD MU SCS OBJD SHRD0;
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep;
      (* [comment removed for export] *)
      lazymatch goal with |- evtA _ _ _ _ (MS ?R ?Fx _ ?fcx ?rv ?mx ?ro) =>
        apply (evtA_cut asegs AL CS (fun ms' => ms' = MS R Fx (Z_to_bv 64 0x68b58) fcx rv mx ro));
        [ zstep; destruct (Z.eq_dec DST SRC) as [E|NE];
          [ if_trueU; apply evtA_done; reflexivity
          | if_falseU; zstep; destruct (Z_lt_le_dec SRC (DST + n));
            [ if_falseU; zstep; if_falseU; apply evtA_done; reflexivity
            | if_trueU; apply evtA_done; reflexivity ] ]
        | ] end;
      cbn beta; intros ms' ->;
      (* [comment removed for export] *)
      zstep; zstep; rewrite zb_lxor_ones by lia; if_falseU;
      (* [comment removed for export] *)
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2160)
          (eapply imemcpy_chkS with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2160)) by lia;
           first [ exact OBJx | exact HULLS | exact SHRD0 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end;
      (* [comment removed for export] *)
      clear SHRD0; shrd_now SHRD MU SCS OBJD SHRD1;
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2160)
          (eapply imemcpy_chkD with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2160)) by lia;
           first [ exact OBJx | exact HULLD | exact SHRD1 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep;
      lazymatch goal with Hd : rw_cells _ ?mx DST [CB ?kk ?bs], Hs : bytes_at _ ?mx SRC ss |- _ (MS _ _ _ _ _ ?mx _) =>
        replace kk with (Z.to_nat n) in Hd by lia;
        callxA (eapply (A_memcpy_evtA_Z AL IMG CS) with (DST := DST) (SRC := SRC) (n := n) (src := ss) (junk := bs);
                [ exact Hs | lia | exact Hd | lia | assumption
                | exact (aobj_crange _ _ _ _ _ _ OBJD) | exact (aobj_crange _ _ _ _ _ _ OBJS)
                | lia | lia | lia | lia | lia | reflexivity | reflexivity | reflexivity ])
      end;
      (* [comment removed for export] *)
      do 13 zstep;
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -80)%Z end;
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FRS H (bv_unsigned sp) end;
      unfold amemcpy_post; finish;
      lazymatch goal with H : rw_cells _ _ DST _ |- u8arr _ _ _ _ => exact (u8arr_of_rw_cells _ _ _ _ _ H) end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

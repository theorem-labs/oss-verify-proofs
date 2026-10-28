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
Ltac2 gd_tbl_A_amemcpy () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.B.A_rip.rip_consts"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.chkS_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.chkD_post"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amem_consts"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amem_apart"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amemcpy_post"].


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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@C17025492443.113C17025492443.88 L11447729190.144L11944109973.88 L13226205188.72 L13230398037.87 L14345069909.69 L18705684095.87 L1918331350.56  L19322770858.87 L19628431903.90 L20966712717.92 L24122754266.92 L24122936649.92 L24124928684.86 L24124928684.87 L24608617390.70 L24982526223.90 L25632820001.0  L25792253067.68 L27196467039.69 L28083348026.88 L29784464483.91 L29786564236.87 L29971684470.70 L31686803170.92 L3248729870.2   L3421674955.92  L34922678286.2  L36929494798.2  L38150352304.92 L39594679749.87 L41312602363.92 L45607281678.2  L46817748388.72 L47543971773.92 L49899794702.2  L51172192526.2  L52065394884.86 L52514161039.90 L53517158443.69 L53519158063.90 L5549769202.92  L61097676998.2  L61932014891.69 L64055233047.92 L64240928084.86 L64596837268.70 L66488557582.2  L7106453518.2   L82129492.72    O14206727921.113O14206727921.88 O15547502833.113O15547502833.88 O17025492443.113O17025492443.88 O23485702385.113O23485702385.88 O32131581681.113O32131581681.88 O38504098033.113O38504098033.88 O4492316913.113 O4492316913.88  O48978854641.113O48978854641.88 O65485481713.113O65485481713.88 P3245129067.113 P3245129067.88  P34917767787.113P34917767787.88 P36941614443.113P36941614443.88 P45611546219.113P45611546219.88 P49904706411.113P49904706411.88 P51184575339.113P51184575339.88 P66501341803.113P66501341803.88 P7102853739.113 P7102853739.88  Q11819106457.88 Q12384979828.87 Q17356333121.87 Q19275945964.87 Q20040127854.87 Q20109487353.87 Q21797814763.87 Q23650890746.91 Q24745328269.91 Q28218390483.91 Q29427030349.87 Q31394395900.87 Q31762069934.91 Q32231604980.87 Q33251509847.87 Q34268098539.87 Q34355500059.88 Q34947676851.87 Q35212026327.87 Q36722057835.87 Q3742509637.87  Q38148316102.87 Q39778974580.87 Q39942779359.87 Q41324687698.91 Q43608312681.88 Q43855177782.87 Q44556843737.91 Q44682733963.91 Q45748806138.91 Q45896845414.87 Q46309744770.91 Q46311840365.87 Q49545476915.87 Q51241282684.87 Q52818999351.87 Q52821082840.91 Q53519998161.87 Q56964988266.87 Q59322611797.87 Q59365683033.87 Q62824840384.87 Q63037122486.87 Q6460837458.87  Q66715486460.87 Q67805910652.87 00000100200300400>00H00O00[00e00l01801F01U01d01e02402=02D02E02J02Q02R02Y02`02l03<03=03P03Q03R03i04804K04L04^04n04o05005<05C05D05K05U05V05[05e06106706806906C06D06E06F06G06R06]06^06_06`06a06b06c06d06e06f06g06h06i07:07E07V07a08208=08N08Y08j09509F09Q09b09m0:>0:I0:U0:V0:W0:e0:f0:g0:h0:i0;<0;G0;H0;O0;P0;Q0;R0;k0<20<30<40<50<60<M0<W0=50=60==0=L0=b0=c0=n0=o0>?0>X0>Y0>`0>a0>b0?20?30?J0?`0@?0@N0@O0@a0A3FFFFS3SRC1n2B0S3SRC1n2B0S1n3BIGS3SRC1n1N2B0S3SRC1n2ARS3SRC1nS3SRC1n1N2B0S3SRC1n2q13Q45S3SRC1n3H8a3H8bS3SRC1n3H8a3H8bFS3SRC1n3H8a3H8bS1n5SMALLS3SRC1nSS1n1NS1n3BIGFS3SRC1nS3SRC1nS3SRC1n1N2NZS3SRC1n2q02q12DBFS3SRC1n2q02q12DB2LTFFS3SRC1n2B02q02q12E03Q01S3SRC1n3H8a3H8bS3SRC1n2q02q12DB2GEFS3SRC1n1N5SMALL2NZS3SRC1n2B05SMALLFFS3SRC1n1N2B0S3SRC1nSS3SRC1nS3SRC1n2GEFS1n1NS3SRC1n2LTS3SRC1n1N2B0S1n2N0FFS3SRC1n2B0FFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S3SRC1n1N2NZFFS3SRC1n2q13Q45FFFFS3SRC1n2B02q02q12DBS3SRC1n3H8bFS3SRC1nFFFS3SRC1n1N2B02q02q13Q012DBS3SRC1nFFFFS3SRC1n2B02q02q12E03Q01S3SRC1n2q0S2AL3SRC1n4IMG'2B02q02q12E12DBFS3SRC1nS2AL3SRC1n4IMG'S2AL3SRC1n4IMG'2B03H8bFS3SRC1n3H8bFS3SRC1n2q02q12DBS3SRC1n1N2B02q02q13Q012DBFS3SRC1nFFS2AL3SRC1n5ALWF'FS3SRC1n2B02q02q13Q452DBS3SRC1n2B02q02q12E12DBS2AL3SRC1n4IMG'2B02q02q12E03Q01S2AL3SRC1n4IMG'FS2AL3SRC1n4IMG'2B0S2AL3SRC1n4IMG'2B0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma amemcpy_chkS : ltac2:(CDefT.buildp (gd_tbl_A_amemcpy ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PDST,$3.PSRC,$3.Pn,$3.Plo,$3.P,(4.$5.VAL,VCS,R5.R3.R2.)P,(6.(7.=R3.)(8.R3.(9.+2.+28.)))P,(:.R5.(;.(;.R5.R4.)+7.))P,P,(7.+1.R5.)(6.(<.VCS,(=.R7.(>.R7.+40.))+40.)(<.VCS,(=.(=.(;.R7.R6.)+1.)(>.(=.(;.R7.R6.)+1.)+40.))+40.))P,Pc,$3.P,A1.VCS,R1.(?.(0.&8.)Lb,(0.&8.)(10.$5.R<.(11.VAL,R3.)(12.(0.&8.)R1.(13.(0.&8.)))))P,(14.R:.)P,(15.$5.R;.R7.(16.&40.R2;.))P,(8.+10007???7???.R8.)P,(7.R9.(=.(16.&40.R2=.)+50.))P,(<.VCS,R:.(=.(16.&40.R2>.)R:.))P,(17.$5.R?.)P,(6.(7.=R?.)(8.R?.(9.+2.+40.)))P,(18.(0.&40.)R29.(19.&40.R10.))P,(18.(0.&40.)R29.(19.&40.R10.))P,(18.(0.&40.)R29.(19.&40.R10.))P,(18.(0.&40.)R21.(19.&40.(;.R12.R11.)))(1:.$5.VAL,VCS,(1;.R35.R34.R33.R2?.R24.R23.R1?.R1>.R1=.R1<.R17.R16.R14.R13.R12.R11.R15.)(1<.(1=.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(19.&40.+67>20.)R16.(1>.(0.&40.))R15.(1?.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI DB0 -> -> -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < SRC /\ SRC + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    Ltac ripS SRC n lo SCS :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := SRC) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep;
      unfold chkS_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. (* [comment removed for export] *) zstep. if_trueU. ripS SRC n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold chkS_post; finish. }
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
    2:{ unfold chkS_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (SRC + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((SRC + n - 1) / 8) 2147450880) in RDk.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (SRC / 8) ((SRC + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply (amemcpy_orloop AL IMG ALWF CS CSOK) with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [left; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (SRC / 8) with ((SRC + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a5' & a6' & ->)).
    (* [comment removed for export] *)
    zstep. zstep.
    if_cases Ks.
    2:{ ripS SRC n lo SCS. }
    unfold chkS_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0280@C17025492443.112C17025492443.87 L11447729190.143L11944109973.87 L14345069909.68 L16029456145.71 L16033656128.86 L19628431903.89 L20966712717.91 L23189051853.55 L2394494565.91  L24122754266.91 L24122936649.91 L24124928684.85 L24124928684.86 L24608617390.69 L24982526223.89 L25792253067.67 L27050710447.71 L27196467039.68 L28083348026.87 L29784464483.90 L29786564236.86 L29971684470.69 L31686803170.91 L31723725750.67 L3248729870.2   L3421674955.91  L34922678286.2  L35539854113.0  L35600352231.67 L35692323376.91 L36929494798.2  L38150352304.91 L39594679749.86 L41794548952.86 L45607281678.2  L46817748388.71 L47543971773.91 L49899794702.2  L51172192526.2  L52065394884.85 L52514161039.89 L53517158443.68 L53519158063.89 L61097676998.2  L61402522944.85 L61402946443.66 L61402946443.67 L61931751947.67 L61932014891.68 L63477229558.86 L6351988974.91  L64596837268.69 L66488557582.2  L7106453518.2   O14206727921.112O14206727921.87 O15547502833.112O15547502833.87 O17025492443.112O17025492443.87 O23485702385.112O23485702385.87 O32131581681.112O32131581681.87 O38504098033.112O38504098033.87 O4492316913.112 O4492316913.87  O48978854641.112O48978854641.87 O65485481713.112O65485481713.87 P3245129067.112 P3245129067.87  P34917767787.112P34917767787.87 P36941614443.112P36941614443.87 P45611546219.112P45611546219.87 P49904706411.112P49904706411.87 P51184575339.112P51184575339.87 P66501341803.112P66501341803.87 P7102853739.112 P7102853739.87  Q10652825868.86 Q12854075564.86 Q19275945964.86 Q21797814763.86 Q23650890746.90 Q24745328269.90 Q25930949378.86 Q28218390483.90 Q29427030349.86 Q31394395900.86 Q34268098539.86 Q34947676851.86 Q36722057835.86 Q3742509637.86  Q37735318614.86 Q38148316102.86 Q39778974580.86 Q39942779359.86 Q41324687698.90 Q43608312681.87 Q43855177782.86 Q44556843737.90 Q45129161346.86 Q45748806138.90 Q46309744770.90 Q46311840365.86 Q49545476915.86 Q49598061100.86 Q51241282684.86 Q52818999351.86 Q52821082840.90 Q53519998161.86 Q54929902563.90 Q56964988266.86 Q58952702441.86 Q59322611797.86 Q59365683033.86 Q62824840384.86 Q63037122486.86 Q63979701653.90 Q6460837458.86  Q66715486460.86 Q6693426778.87  Q67304791703.87 Q67805910652.86 Q67834060547.86 00000100200300400;00E00O00[00i01301=01L01[01\01k02402;02@02J02Q02R02Y02`02l03<03F03G03Z03[03\03h04204304J04Y04`04a05305C05D05E05Q05X05Y05`05a05m06906E06J06O06[06n07407507607707807907:07E07P07Q07R07S07T07U07V07W07X07Y07Z07[07\07m08808I08T08e09009A09L09]09h0:90:D0:U0:`0;10;<0;=0;>0;L0;M0;N0;a0;b0;m0;n0<50<N0<O0<P0<Q0<R0<i0=30=Q0=R0=Y0=h0>>0>?0>J0>Z0?30?40?50?<0?=0?>0?N0?O0?P0?Q0?h0@>0@]0@l0@m0@n0A@0AG0AS0Ae0AfFFFFS1n3BIGS3DST1n2B0S3DST1n2B0S3DST1n1N2B0S3DST1n2q13Q45S3DST1n2ARS3DST1n2GES3DST1n3H8a3H8bS3DST1n3H8a3H8bFS3DST1n3H8a3H8bS1n5SMALLS3DST1nS1n1NS3DST1n2B0S1n3BIGFS3DST1nS3DST1nS3DST1n1N2NZS3DST1n2q02q12DBS3DST1n2B0FS3DST1n2q02q12DB2LTFSS3DST1n1N2B0S3DST1n2LTFS3DST1n2B02q02q12E03Q01S3DST1n3H8a3H8bS3DST1nFS3DST1n1N5SMALL2NZS3DST1n2B05SMALLFFS3DST1n1N2B0S3DST1nSS3DST1nFS3DST1n1N2B0S3DST1n1N2B0S3DST1n1N2B0S1n1NS1n1NS3DST1n1N2B0S3DST1n2q02q12DB2GES1n2N0FFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0FFS3DST1n2q13Q45FFS3DST1n2B02q02q12DBFS3DST1n3H8bFS3DST1nS3DST1n1N2B02q02q13Q012DBFFFFS3DST1n2B02q02q12E03Q01S3DST1n2q0S2AL3DST1n4IMG'2B02q02q12E12DBFS3DST1nS2AL3DST1n4IMG'S2AL3DST1n4IMG'2B03H8bFS3DST1n3H8bS3DST1n2q02q12DBS3DST1n1N2B02q02q13Q012DBFFS3DST1nFFS2AL3DST1n5ALWF'FFFS3DST1n2B02q02q13Q452DBS3DST1n2B02q02q12E12DBS2AL3DST1n4IMG'2B02q02q12E03Q01S2AL3DST1n4IMG'FFS2AL3DST1n4IMG'2B0S3DST1nS3DST1n1N2NZS2AL3DST1n4IMG'2B0F". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma amemcpy_chkD : ltac2:(CDefT.buildp (gd_tbl_A_amemcpy ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PDST,$3.PSRC,$3.Pn,$3.Plo,$3.P,(4.$5.VAL,VCS,R5.R4.R2.)P,(6.(7.=R3.)(8.R3.(9.+2.+28.)))P,(:.R6.(;.(;.R6.R4.)+7.))P,P,(7.+1.R5.)(6.(<.VCS,(=.R8.(>.R8.+40.))+40.)(<.VCS,(=.(=.(;.R8.R6.)+1.)(>.(=.(;.R8.R6.)+1.)+40.))+40.))P,Pc,$3.P,A1.VCS,R1.(?.(0.&8.)Lb,(0.&8.)(10.$5.R<.(11.VAL,R3.)(12.(0.&8.)R1.(13.(0.&8.)))))P,(14.R:.)P,(15.$5.R;.R7.(16.&40.R2;.))P,(8.+10007???7???.R8.)P,(7.R9.(=.(16.&40.R2=.)+50.))P,(<.VCS,R:.(=.(16.&40.R2>.)R:.))P,(17.$5.R?.)P,(6.(7.=R>.)(8.R>.(9.+2.+40.)))P,(18.(0.&40.)R29.(19.&40.R10.))P,(18.(0.&40.)R29.(19.&40.R10.))P,(18.(0.&40.)R29.(19.&40.R10.))P,(18.(0.&40.)R23.(19.&40.(;.R13.R11.)))P,(18.(0.&40.)R21.(19.&40.(;.R12.-41.)))(1:.$5.VAL,VCS,(20.R36.R35.R34.R30.R24.R22.R20.R1?.R1>.R1=.R18.R17.R15.R14.R13.R12.R16.)(1<.(1=.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(19.&40.+67>64.)R17.(1>.(0.&40.))R16.(1?.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI SB0 -> -> -> -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < DST /\ DST + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    Ltac ripD DST n lo SCS :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := DST) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep; zstep;
      unfold chkD_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. rewrite zb_lxor_ones by lia. if_falseU.
    zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. (* [comment removed for export] *) zstep. if_trueU. ripD DST n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold chkD_post; finish. }
    replace ((1 <=? n) && (n <=? 64))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
    if_falseU.
    destruct (HULL ltac:(lia)) as [HULL0 HULL1].
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m DST n OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    qc_block DST n E0 E1.
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold chkD_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (DST + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((DST + n - 1) / 8) 2147450880) in RDk.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (DST / 8) ((DST + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply (amemcpy_orloop AL IMG ALWF CS CSOK) with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [right; left; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (DST / 8) with ((DST + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a5' & a6' & ->)).
    zstep. zstep.
    if_cases Ks.
    2:{ ripD DST n lo SCS. }
    unfold chkD_post; finish.
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0520@C17025492443.118C17027589631.137C29675049067.152K21979204025.152K47064714985.151K58434789865.151K61309466857.151K65658691719.152L11123517328.1  L11239731393.4  L11255914340.96 L11518786483.141L11518786483.88 L12561043416.141L12561043416.88 L13136158964.98 L13225815175.133L13454883133.2  L14374941206.2  L14826010361.133L16029064082.133L16076420852.87 L16852238724.148L17751112592.1  L1860589272.141 L1860589272.88  L19006798410.96 L19556266785.0  L20076479292.146L20146841363.2  L2025501661.3   L20652354682.98 L20808779268.98 L21990708291.2  L22015551912.3  L22101885812.88 L23267971501.73 L2423253472.133 L25796462353.114L25796462354.96 L26130624665.4  L2666392125.2   L27501889588.96 L27501889591.114L28113342964.88 L28563140627.2  L28860711850.98 L29441512509.2  L30284306320.1  L30400651808.147L30620568692.88 L31245493021.96 L31245493022.114L32460099653.2  L33818746643.2  L35265264016.1  L36914643987.2  L37819470141.2  L38250533172.96 L38250533175.114L38645582680.147L40294402896.1  L4038446068.88  L40691620147.2  L41010467417.133L42823025544.133L43055353660.90 L43877851624.96 L43877851627.114L44549549206.2  L44590266200.141L44590266200.88 L45800883475.2  L46229568912.1  L46638324410.4  L46806245891.92 L47075365651.2  L48151489112.141L48151489112.88 L49092413757.2  L49129331261.2  L49220693398.133L50169871760.1  L51728444760.141L51728444760.88 L52499634749.2  L53544459352.141L53544459352.87 L54207053188.97 L5422860760.141 L5422860760.88  L54243326995.2  L54422382992.1  L54668938301.2  L54708048500.88 L55641221123.88 L55843909098.3  L58119466785.95 L58130246816.113L58323406181.94 L58423753747.2  L60268184117.114L60268184118.96 L60290246322.134L60716802292.88 L61320439059.2  L61390376978.96 L61398538917.97 L61398912846.98 L61400521381.97 L61935960466.96 L63529291102.98 L63975535526.133L64243071665.97 L64244674394.98 L64245054129.97 L64253079557.114L64253079558.88 L64253079558.96 L64319148573.2  L64788204432.1  L65018549478.92 L65655075046.4  L65868959243.1  L6610646974.97  L66493423933.2  L66744909172.88 L66975143786.3  L67275561872.1  L68354046352.1  L8064833853.2   L8830339091.2   L9000864984.141 L9000864984.88  N21303764596.138N27801652866.138N44259866089.119N64040766665.119O14206727921.118O14208825045.137O15545405653.137O15547502833.118O17025492443.118O17027589631.137O23485702385.118O23487799509.137O28953822661.137O28955919841.118O29675049067.152O30179188619.151O30286673803.151O32129484501.137O32131581681.118O34072225748.152O3521469857.152 O35907574667.151O38504098033.118O38506195157.137O42849031057.118O42851128245.137O43116495243.151O4352777611.151 O4492316913.118 O4494414037.137 O45584088819.118O45586185943.137O48635945867.151O48978854641.118O48980951765.137O50651377905.118O50653475029.137O52201094539.151O54335600011.151O55436697483.151O62532530571.151O65483384533.137O65485481713.118O66103434849.151O66254176497.118O66256273621.137O7921967435.151 O9829674324.152 P11136886036.98 P11136886036.99 P11225555076.137P11227652256.118P13440002940.137P13442100056.118P17762908436.98 P17762908436.99 P20140522217.151P2020832220.98  P2020832220.99  P21979204025.152P22027872681.98 P22027872681.99 P26127147256.118P26129244380.137P2650994812.137 P2653091928.118 P28568546793.151P29428729432.118P29430826620.137P30297150740.98 P30297150740.99 P33813332713.151P35252419348.98 P35252419348.99 P36925037033.151P37830017916.137P37832115032.118P40289946068.98 P40289946068.99 P40697808073.151P45791156457.151P46232977172.98 P46232977172.99 P46625147103.151P49103625084.137P49105722200.118P49133717592.118P49135814780.137P50173804308.98 P50173804308.99 P52510050428.137P52512147544.118P54249710057.151P54410586900.98 P54410586900.99 P54665076312.118P54667173500.137P55836798992.152P64312787036.137P64314884216.118P64783223060.98 P64783223060.99 P66498474840.118P66500572028.137P66985659024.152P67262191892.98 P67262191892.99 P68366891796.98 P68366891796.99 P8059128700.137 P8061225816.118 P8841319913.151 Q13482121755.95 Q15643324129.94 Q15647878503.148Q17974635083.95 Q18361895783.148Q18363828454.95 Q2186089982.133 Q21877548677.95 Q21892523268.148Q24394897947.95 Q25513505925.97 Q25513505925.98 Q27582847718.95 Q27597822311.148Q27905103109.95 Q27911231108.148Q30402748932.148Q30412939653.95 Q31258583015.148Q31269428326.95 Q32653403622.95 Q32659924583.148Q33251554080.95 Q33913700356.148Q33916158853.95 Q35419777341.152Q36330714342.152Q36423785477.95 Q36438237060.148Q36722022172.95 Q38248387216.118Q38250484404.137Q3832524549.95  Q3834260612.148 Q39935065476.148Q39941651973.95 Q41139448935.148Q41154490342.95 Q43855338817.95 Q43877802600.137Q43879899724.118Q4454393706.96  Q44650941030.95 Q44652743143.148Q46025024389.133Q46793571298.97 Q46793571298.98 Q48357790137.98 Q49598033755.95 Q49698585326.96 Q49698585326.97 Q51000317356.95 Q51223049447.148Q51233699686.95 Q51241048331.95 Q5318114788.133 Q53519968678.95 Q53532715523.133Q54894609875.95 Q54894609875.96 Q57916578385.95 Q58215755193.133Q59830194919.148Q59841040742.95 Q60268184117.114Q60268184118.96 Q62283281657.98 Q62283281657.99 Q64191759790.133Q64536302640.95 Q66524164229.95 Q66534486788.148Q67806143243.95 Q8528270766.133 Q9838812676.148 Q9843367298.94  00000100200300400]01F02302j02k02l03@03J03T03^03h04;04O04P04W05e06906C06T06U06_06i07X07Y07c07d07e08Z08m08n08o0990:I0:]0;30;I0;J0;K0;L0;M0;W0;X0<E0<F0<G0<X0<b0=30=D0=E0=F0=G0=H0=I0=S0=]0=g0=h0>20>30>G0>U0>f0?30?@0?G0?Q0?[0?\0?]0?^0?o0@00@:0@D0@E0@F0@Y0@Z0@d0@n0@o0A90AC0BR0B\0Bf0Bg0Bh0Bi0C30C=0C>0CK0CX0Cb0Cc0D<0DU0D\0Df0Dg0EV0Eo0F^0GM0Gc0I60IJ0J90Jj0KE0L40Lc0MR0MS0MT0M^0M_0Mc0NQ0NR0N\0N]0N^0N_0N`0Na0Nk0O50OH0O[0On0PA0PB0PC0PD0PE0PP0P[0P\0P]0P^0P_0P`0Pa0Pb0Pc0Pd0Pe0Pf0Pg0Ph0Pi0Pj0Pk0Pl0Pm0Pn0Po0Q00Q10Q20Q30Q40Q50Q60Q70Q80Q90Q:0Q;0Q<0Q=0Q>0Q?0Q@0QA0Qh0Rd0SB0S`0T10TB0Ti0Ue0VN0WB0XK0XL0Y@0ZI0Zg0[E0[V0[g0\P0\a0]20]Y0^U0_>0_e0`a0aJ0a[0al0bS0cO0d80da0eH0fD0f]0fn0g?0gP0ga0hH0iD0iU0if0jO0k60l20lC0lT0m10mB0mS0n:0o60oG0oX10510\11X12?13;13L13]14F14M14Z14g14h15515B15C15T15e16416S17G17T17a18218C18T18e19219?19L19Y19Z19k1:<1:I1:T1:e1;61;71;A1;K1;\1;m1<>1<O1<\1<i1=81=E1=R1=_1=l1>91>:1>]1?R1@51@61@M1@d1@e1A21A?1AF1AU1Ae1B51BB1BO1B^1B_1Bl1C91CR1Ck1DT1ER1EY1EZ1Ek1F<1FK1FZ1Fk1G<FFFFS3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP43AP22sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss4LENS3SEP2B02sp2lo3SPL5DISJD5DISJS3LO0FFS3DST3SRC1n2ds2ss2B0S2sp2ds2ssS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss1lS3DST3SRC1n2ds2ss2B0FS2sp2loS3DST3SRC1n2ds2ss3SEP3ARD3ARS3AP13AP23AP33AP43AP52B02sp2lo3SPL5DISJD5DISJS3LO0S3DST3SRC1n2ds2ss2B0S2sp2ds2ssS2sp2lo2ds2ss3SPLFS2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSSS2sp2ds2ssFFS3DST3SRC1n2ds2ss2B01l4LEND2sp2lo3LO03SPL5DISJS5DISJDS3DST3SRC1n2ds2ss1lFFS2sp2ds2ssS2sp3DST3SRC1n2lo2ds2ss4LEND3SEP3ARD3ARS3AP13AP23AP33AP43AP53LO03SPL5DISJD5DISJSS3DST3SRC1n2ds2ss2B0S3DST3SRC1n2ds2ss1N2B0S3DST3SRC1n2ds2ss1N2B0FFFFS2sp2ds2ssFS3DST3SRC1n2ds2ss4LEND2B02sp2lo3LO03SPL5DISJSFFS2sp2lo2ds2ss3SPLS2sp2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLFFFFFS2lo2ds2ssS2lo2ds2ssS2sp2ds2ssFS2sp2ds2ssFS3DST3SRC1n2ds2ss2B0S1n2ds2ss4LENDS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2loS2sp2ds2ssS2sp2ds2ssFFFS2sp2lo2ds2ss3SPLFS2sp2ds2ssS2sp2ds2ssFFS1n2ds2ss4LEND4LENSFS2sp2ds2ssS2sp2ds2ssFS2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss4LEND3ARD3ARS3AP13AP23AP33AP43AP52NE2sp2lo3SPL5DISJD5DISJS3LO0S2sp2ds2ssS2sp2ds2ssFFFS2sp2ds2ssS2sp2ds2ssFS3DST1n2ds2ssS3DST1n2ds2ssS2sp2ds2ssFS2sp2lo2ds2ss3LO03SPL3SPRS2sp2lo2ds2ss3LO03SPL3SPRS2ds2ssS2sp2ds2ssFS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B0S3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss1N2B0S3DST3SRC1n2ds2ss3SEP3ARD3ARS3AP13AP23AP33AP43AP52B02NE1l2sp2lo3SPL5DISJD5DISJS3LO0S3DST3SRC1n2ds2ss2B0S3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss2B01l4LEND2sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B01ES3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSFFS2sp2ds2ssFS2spS3DST3SRC2ds2ss1E2sp1n2lo4LEND3SPL5DISJD5DISJSFS2sp2ds2ssFFFFFS2sp2ds2ssS2sp2ds2ssS2sp2lo2ds2ss3x361CS2sp2lo2ds2ss3x361CS2sp2lo2ds2ss3x171CS2sp2lo2ds2ss3x171CFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp3SRC1n2lo2ds2ss4LENS5DISJSS2sp3SRC1n2lo2ds2ss4LENS5DISJSS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2ra2sp3DST1n2lo2ds2ss4LEND3SPL5DISJD2HB5Ha_st5Hl_stS2sp2s03DST1n2lo2ds2ss4LEND3SPL5DISJD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS2ra2sp3SRC1n2lo2ds2ss4LENS3SPL5DISJS2HB5Ha_st5Hl_stS2sp2s03SRC1n2lo2ds2ss4LENS3SPL5DISJS2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp3DST1n2lo2ds2ss4LEND5DISJDS2sp3DST1n2lo2ds2ss4LEND5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp3DST1n2lo2ds2ss5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp3DST1n2lo2ds2ss3SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp3DST1n2lo2ds2ss3SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2AL2ds2ss4IMG'S2ra2sp2lo2ds2ss2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS3DST1n2ds2ssS3DST2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLFS2lo2ds2ssS2lo2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2AL2ds2ss4IMG'S2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2ds2ss2HBS2sp2lo2ds2ssS2sp2lo2ds2ssFS2ra2sp2lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp2s72lo2ds2ss3SPL2HB5Ha_st5Hl_stFS2sp2ds2ss3SPR2HB5Ha_stS2sp2ds2ss3SPR2HB5Ha_stFS2sp2lo2ds2ssS2sp2lo2ds2ssS2ds2ssS2AL2ds2ss4IMG'S2AL2ds2ss5ALWF'S2AL2ds2ss5ALWF'S2sp2ds2ss2HBS2sp2ds2ss2HBS2AL2ds2ss4IMG'FS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ss3LO03SPL3SPRS2sp2lo2ds2ss3LO03SPL3SPRS2ra2sp3DST1n2lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2s03DST1n2lo2ds2ss3SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2ds2ssFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2AL2ds2ss4IMG'S2AL2ds2ss4IMG'S2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Theorem amemcpy_spec : ltac2:(CDefT.buildp (gd_tbl_A_amemcpy ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PDST,$3.PSRC,$3.Pn,$3.Plo,$3.Pds,(21.(0.&8.))Pss,(21.(0.&8.))P,(22.$5.R7.R6.R2.)P,(10.$5.R8.R6.R2.)P,(18.$3.(23.(24.(0.&8.)R4.))R6.)P,(18.$3.(23.(24.(0.&8.)R4.))R7.)P,(4.$5.VAL,VCS,R;.R:.R8.)P,(4.$5.VAL,VCS,R<.R:.R9.)P,(25.(18.$3.R:.=)(25.(7.(;.R<.R:.)R;.)(7.(;.R;.R:.)R<.)))P,(8.R;.(9.+2.+28.))P,(:.R>.(;.(;.R>.R<.)+7.))P,(:.R>.(;.(;.R>.R=.)+7.))P,P,(7.+1.R>.)(6.(<.VCS,(=.R11.(>.R11.+40.))+40.)(<.VCS,(=.(=.(;.R11.R?.)+1.)(>.(=.(;.R11.R?.)+1.)+40.))+40.))P,P,(7.+1.R?.)(6.(<.VCS,(=.R11.(>.R11.+40.))+40.)(<.VCS,(=.(=.(;.R11.R10.)+1.)(>.(=.(;.R11.R10.)+1.)+40.))+40.))P,Pc,$3.P,A1.VCS,R1.(?.(0.&8.)Lb,(0.&8.)(10.$5.R16.(11.VAL,R3.)(12.(0.&8.)R1.(13.(0.&8.)))))P,(26.R14.)P,(27.R14.R12.)P,(15.$5.R16.R12.(16.&40.R36.))P,(8.+10007???7???.R13.)P,(7.R14.(=.(16.&40.R38.)+8;0.))P,(<.VCS,R15.(=.(16.&40.R39.)R15.))P,(25.(7.(;.R19.R17.)R16.)(7.(16.&40.R3:.)R19.))P,(25.(7.(;.R19.R18.)R17.)(7.(16.&40.R3;.)R19.))P,(17.$5.R1<.)P,(18.(0.&40.)R35.(19.&40.R1<.))P,(18.(0.&40.)R35.(19.&40.R1<.))P,(18.(0.&40.)R35.(19.&40.R1<.))(1:.$5.VAL,VCS,(28.R41.R40.R3?.R3>.R3:.R39.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R22.R21.R1?.R1>.R1=.R1<.R1:.R20.)(1<.(1=.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R22.(19.&40.+67=;<.)R21.(1>.(0.&40.))R20.(1?.$5.)))")
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
      carve_frame 72%nat ST; rename FR into FRS; carve_frame 2072%nat ST;
      (* [comment removed for export] *)
      do 16 zstep;
      (* [comment removed for export] *)
      shrd_now SHRD MU SCS OBJD SHRD0;
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep;
      (* [comment removed for export] *)
      lazymatch goal with |- evtA _ _ _ _ (MS ?R ?Fx _ ?fcx ?rv ?mx ?ro) =>
        apply (evtA_cut asegs AL CS (fun ms' => ms' = MS R Fx (Z_to_bv 64 0x67e18) fcx rv mx ro));
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
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemcpy_chkS with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLS | exact SHRD0 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end;
      (* [comment removed for export] *)
      clear SHRD0; shrd_now SHRD MU SCS OBJD SHRD1;
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemcpy_chkD with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
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
      do 12 zstep;
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -72)%Z end;
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FRS H (bv_unsigned sp) end;
      unfold amemcpy_post; finish;
      lazymatch goal with H : rw_cells _ _ DST _ |- u8arr _ _ _ _ => exact (u8arr_of_rw_cells _ _ _ _ _ H) end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

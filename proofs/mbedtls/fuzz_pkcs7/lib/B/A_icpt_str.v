(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip A_amem_lib A_icpt_read.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA Restrict RestrictLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_memchr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Ltac2 gd_tbl_A_icpt_str () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.B.A_rip.rip_consts"; "Walk.sarg_post"; "Walk.mc_chk_post"; "Walk.sn_chk_post"].


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L14404048632.3L14657277159.3L19881737346.3L21824615802.3L33064235947.3L41991022032.3L59872977917.300000300900>00C00K00Q00YS1LS1L2HLS1L1lS1L1lS1L2HL1lS1L2HLS1L2HL1l". (* [comment removed for export] *)
Lemma ltu_m65 : forall L, 0 <= L < 2^40 ->
  bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (L + -64)) = (L <? 64).
Proof.
  intros L HL. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace ((-65) mod 18446744073709551616) with 18446744073709551551 by reflexivity.
  destruct (Z_lt_le_dec L 64).
  - replace ((L + -64) mod 18446744073709551616) with (18446744073709551616 + (L - 64)).
    2:{ apply Z.mod_unique with (q := -1); lia. }
    replace (L <? 64) with true by (symmetry; apply Z.ltb_lt; lia). apply Z.ltb_lt. lia.
  - replace ((L + -64) mod 18446744073709551616) with (L - 64) by (symmetry; apply Z.mod_small; lia).
    replace (L <? 64) with false by (symmetry; apply Z.ltb_ge; lia). apply Z.ltb_ge. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L10351953861.56L20250526293.52L34196651870.61L3434582503.61 L3443773003.53 L37976990582.51L38310105965.52L40039588104.55L44409180458.61L52123366153.56L53519254704.61L59309007591.57L9864819516.61 Q20632073342.61Q29624500871.52Q39007695549.52Q48990496914.6100000=00H00R00b00j01001601C01R01_01i02<02T02c02n03603ES1k1i1s2Hk2HiS1i1s2Hk2HiS1k1i1s2HkS1k1i1s2Hk2Hi2NES1k1s2HkS1s2HkS1s2HkS1k1i1s2Hk2HiS1k1i1s2Hk1b2BRS1k1i1s2Hk2HiS1k1i1s2HkS1k1i1s2Hk2Hi2NE2SKS1k1i1s2Hk2Hi2NE1b2Hb2BRS1k1i1s1P2Hk2HiS1s1P2Hi2HkS1s1P2HkS1k1i1s1P2Hk2Hi". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma istrlen_loop : ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Pk,$0.Pi,$1.Ps,(2.(3.&8.))PP,$1.Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))P,(6.(7.(8.(9.(3.&8.)R23.))R24.)(8.R25.))P,(:.(6.=R25.)(6.R25.(8.(9.(3.&8.)R24.))))P,(;.$<.R3.R24.(=.(3.&8.)R25.(>.(3.&8.)(?.&8.=)(10.(3.&8.)))))P,(11.(12.(3.&8.)(?.&8.=)R26.))P,(13.VCS,R26.(14.(8.(9.(3.&8.)R27.))+1.))P,(15.=R27.)P,(15.(14.(14.R28.(8.(9.(3.&8.)R29.)))+1.)(16.+2.+3?.))P,(17.(3.&40.)R1?.(?.&40.R2;.))(18.$<.VAL,VCS,Lms',$19.(17.$19.R1.(1:.(1;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.(?.&40.R2;.)(?.&40.(14.(8.(9.(3.&8.)R2<.))+1.))(?.&40.=)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(?.&40.+7:;<0.)R;.(1<.(3.&40.))R:.(1=.$<.)))(1:.(1;.R29.R28.R27.R26.R25.R24.R23.R22.R21.(?.&40.R2:.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R;.(?.&40.+7:;;0.)R:.(1<.(3.&40.))R9.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros Hk Hi BY NZ CR P0 PH ->; al_facts.
    - (* [comment removed for export] *)
      assert (i = Z.of_nat (length s)) as -> by lia.
      pose proof (bytes_at_rdn asegs m P _ (length s) 1 BY ltac:(rewrite length_app; cbn; lia)) as RD.
      rewrite skipn_app, skipn_all2, Nat.sub_diag in RD by lia. cbn [skipn firstn app] in RD.
      unfold wa in RD. rewrite <- ov_rdn in RD.
      zstep. zstep. zstep. zstep. try if_falseU. finish.
    - destruct (Z.eq_dec i (Z.of_nat (length s))) as [-> | NE].
      + eapply (IH (Z.of_nat (length s))); eauto; lia.
      + pose proof (bytes_at_rdn asegs m P _ (Z.to_nat i) 1 BY ltac:(rewrite length_app; cbn; lia)) as RD.
        rewrite Z2Nat.id in RD by lia.
        rewrite skipn_app in RD. replace (Z.to_nat i - length s)%nat with 0%nat in RD by lia. cbn [skipn] in RD.
        destruct (skipn (Z.to_nat i) s) as [|b rest] eqn:SK.
        { exfalso. apply (f_equal (@length byte)) in SK. rewrite length_skipn in SK. cbn in SK. lia. }
        cbn [firstn app] in RD. unfold wa in RD. rewrite <- ov_rdn in RD.
        assert (Hb : bv_unsigned b <> 0).
        { intros Hz. apply NZ. replace (Z_to_bv 8 0) with b by (apply bv_eq; rewrite Hz; reflexivity).
          rewrite <- (firstn_skipn (Z.to_nat i) s), SK. apply in_app_iff. right. left. reflexivity. }
        pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn [Z.pow Z.of_N Pos.pow] in BR.
        zstep. zstep. zstep. zstep. if_trueU.
        eapply (IH (i + 1)); eauto; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L16405147374.59L29644601389.59L30095897756.55L32827618306.50L35469551417.59L48379326627.59L53520163529.59L53520247005.59L56775215785.59L56775393469.59Q17581378383.58Q35222541774.58Q39502766003.58Q4111067988.58 Q52324771135.5800000C00P00f02Z02m03703U04604T05505K05L05\06006JS1k1p1q2lo2Hk2Hp2NES1k1p1q2Hk2NES1k1p1q2lo2hi2Hk2Hp2HqS2AL2CS1p1q2ra2sp2gp2tp2t02t12t22s02s12a22a32a42a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo2Hk2HpS1k1p1q2lo2Hk2Hp2EQS1k1p1q2HkS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2HqFS1k1p1q2lo2Hk2HpS1k1p1q2lo2Hk2Hp3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pc_orloop : ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Pk,$0.Pp,$1.Pq,$1.Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Plo,$1.Phi,$1.P,(6.(7.R23.R24.)(8.R25.))P,(:.(6.R3.R25.)(15.R25.R24.))P,(6.R25.R3.)P,(15.R4.(16.+2.+3?.))P,(6.=R6.)P,Px,$1.P,(:.(6.R8.R1.)(15.R1.R7.))(1>.(3.&8.)Lb,(3.&8.)(;.$<.R;.R3.(>.(3.&8.)R1.(10.(3.&8.)))))P,Px,$1.P,(:.(6.R9.R1.)(15.R1.R8.))(1?.VAL,VCS,R2.)(18.$<.VAL,VCS,Lms',$19.(1>.(3.&40.)La2',(3.&40.)(1>.(3.&40.)La3',(3.&40.)(17.$19.R3.(1:.(1;.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.(?.&40.R2=.)(?.&40.R2=.)R2.R1.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(?.&40.+5;624.)R>.(1<.(3.&40.))R=.(1=.$<.)))))(1:.(1;.R29.R28.R27.R26.R25.R24.R23.R22.R21.(?.&40.R2;.)(?.&40.R2:.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(?.&40.+5;614.)R;.(1<.(3.&40.))R:.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until hi; intros Hk Hp Hq Hhi Hlo RD AOK; [lia|]. al_facts.
    destruct (RD p ltac:(lia)) as [b B]. pose proof (bytes_at_read1 _ _ _ _ B) as RDB.
    zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec (p + 1) q) as [EQ|NE].
    - if_falseU. rewrite EQ. finish.
    - if_trueU. eapply IH; try eassumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition sarg_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Lms',$19.(1>.(3.&40.)Lra,(3.&40.)(1>.(3.&40.)Lt0,(3.&40.)(1>.(3.&40.)Lt1,(3.&40.)(1>.(3.&40.)Lt2,(3.&40.)(1>.(3.&40.)La0,(3.&40.)(1>.(3.&40.)La1,(3.&40.)(1>.(3.&40.)La2,(3.&40.)(1>.(3.&40.)La3,(3.&40.)(1>.(3.&40.)La4,(3.&40.)(1>.(3.&40.)La5,(3.&40.)(1>.(3.&40.)La6,(3.&40.)(1>.(3.&40.)La7,(3.&40.)(1>.(3.&40.)Ls7,(3.&40.)(1>.(3.&40.)Lt3,(3.&40.)(1>.(3.&40.)Lt4,(3.&40.)(1>.(3.&40.)Lt5,(3.&40.)(1>.(3.&40.)Lt6,(3.&40.)(1>.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(:.(17.$19.R13.(1:.(1;.R12.O12.O11.O10.R11.R10.R?.O?.O>.R>.R=.R<.R;.R:.R9.R8.R7.O=.O<.O;.O:.O9.R6.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(?.&40.+5;504.)O3.(1<.(3.&40.))R1.(1=.$<.)))(:.(20.(>.(21.$1.$1.)(22.$1.$1.O2.(23.&40.O12.))(10.(21.$1.$1.)))O1.R1.)(:.(24.$<.O1.R1.)(:.(25.$<.R1.)(26.$<.R1.O2.(23.&40.O12.))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02K0@C17025492443.116C17025492443.94 L10532665219.63 L10642994239.74 L11447729323.155L11668818640.74 L11668818640.75 L11671109536.90 L11944109973.92 L13946194139.98 L13948180391.76 L17423148388.96 L17820268298.76 L1952302740.91  L1954493412.74  L1956330362.76  L19628431903.94 L19885240167.76 L20966712717.96 L21816074906.76 L22721961905.76 L24122754266.96 L24122936649.96 L24124928684.90 L24124928684.91 L24982526223.94 L25731758752.64 L28083348026.92 L2810144006.91  L28552145834.76 L29784464483.95 L29786564236.91 L30124523164.75 L31686803170.96 L31911041468.75 L31913121063.76 L3248729870.2   L33139774177.96 L3421674955.96  L34922678286.2  L36929494798.2  L37862823410.98 L37865032334.76 L38150352304.96 L39594679749.91 L40387107599.76 L45165531934.91 L45607281678.2  L46700662962.76 L47543971773.96 L49899794702.2  L50296483778.96 L5054181744.75  L51172192526.2  L52065394884.90 L52514161039.94 L53517158443.76 L53519158063.94 L61097676998.2  L63950803142.75 L64082510163.74 L64970827566.4  L64977119667.4  L65809642273.0  L66488557582.2  L7106453518.2   L832385313.74   O14206727921.116O14206727921.94 O15547502833.116O15547502833.94 O17025492443.116O17025492443.94 O23485702385.116O23485702385.94 O29478932113.117O29478932113.119O29478932113.95 O29478932113.97 O32131581681.116O32131581681.94 O38504098033.116O38504098033.94 O4492316913.116 O4492316913.94  O48978854641.116O48978854641.94 O65485481713.116O65485481713.94 P3245129067.116 P3245129067.94  P34917767787.116P34917767787.94 P36941614443.116P36941614443.94 P45611546219.116P45611546219.94 P49904706411.116P49904706411.94 P51184575339.116P51184575339.94 P64967619915.117P64967619915.119P64967619915.95 P64967619915.97 P66501341803.116P66501341803.94 P7102853739.116 P7102853739.94  Q12781370905.92 Q14673372720.91 Q15643823314.91 Q16263154483.91 Q19275945964.91 Q21773766844.91 Q21797814763.91 Q24745328269.95 Q26151546087.95 Q28218390483.95 Q29427030349.91 Q30057916957.91 Q31394395900.91 Q34268098539.91 Q34501421650.91 Q36722057835.91 Q38148316102.91 Q39778974580.91 Q39942779359.91 Q41324687698.95 Q43608312681.92 Q43855177782.91 Q44556843737.95 Q45514747608.91 Q45748806138.95 Q46309744770.95 Q46311840365.91 Q47282368501.91 Q47312252080.91 Q51241282684.91 Q51260952339.92 Q52818999351.91 Q52821082840.95 Q53500367258.91 Q53519998161.91 Q54173355287.91 Q57150186488.95 Q59322611797.91 Q59365683033.91 Q61975411717.95 Q62698369181.91 Q62824840384.91 Q63037122486.91 Q6460837458.91  Q66715486460.91 Q67805910652.91 00000100200900A00B00M00Y00d00e01301?01K01W01c01m02902D02O02_02l03503F03W03X03i03n04:04;04G04Q04Z04c04o05A05M05Y05Z05f06;06<06=06I06U06n07?07O07X07Y07`08208308H08T08U08`08e08l09109209>09H09I09J09K09L09M09R09S09T09U09V09g0:80:90::0:;0:<0:=0:>0:?0:@0:A0:B0:C0:D0:E0:F0:G0:H0:[0:l0;?0;P0;c0<40<G0<X0<k0=<0=O0=`0=a0=b0=c0=d0>70>H0>[0>l0?50?60?70?80?H0?I0?J0?_0?`0?m0?n0?o0@80@Q0@R0@S0@l0A80AX0AY0Ab0B30BK0BL0BY0Bk0CD0CE0CF0CO0C[0C\0C]0C^0D00D10D20DK0Dc0Dd0De0EF0EW0EX0El0F@FFS3str1LS3str2L0FS1P1L2L02B0S3str1P1L2B0S1P1L2L02B0FS3str1P1L1N2L0S3str1L1N2L0S3str1P1L2LTS3str1P1L2B0S3str1P1L2B0S3str1P2B0S3str1P1L2B0S1P1L2L02B0S3str1L3BIGS3str1P1L2q13Q45S3str1L5SMALLS3str1P1LS3str1P1L3H8a3H8bS3str1P1L3H8a3H8bFS3str1P1L3H8a3H8bS1P1LS3str1P1L2ARFS3str1P1L2B0S3str1L2L0S3str1P1LS3str1P1LS3str1P1L2B0S3str1P1L2q02q12DBS3str1L1N2L0S3str1L1N2L0FS3str1P1L2GES3str1P1L2q02q12DB2LTFFS3str1P1L2ARS3str1P1L2ARS3str1P1L2B02q02q12E03Q01S3str1P1L3H8a3H8bS3str1L2L05SMALLS3str1P1LFS3str1LS3str1P1L2B05SMALLFS3str1P1L2q02q12DB2GES3str1L1N2L0FS1P1L2L02B0S1P1LS3str1LS1P1LFS3str1P1L2B0S3str1P2B0FFSFFS3strFFFFS2sp3str2lo1L3SPLS2sp3str2lo1L3SPLFFFFFFFFFFFFFFFFS2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0S2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0S2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0S2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0S2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0S2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0FFFFS2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0S2sp3str1P2lo1L3LO0S2sp3str2lo1L3LO0S3str1P1LFFFS3str1P1L2q13Q45FFS3str1P1L2B02q02q12DBFS3str1P1L3H8bFFS3str1P1LS3str1P1L2B02q02q13Q012DBFFS3str1P1L2B02q02q12E03Q01S3str1P1L2q0S2AL3str1P1L4IMG'2B02q02q12E12DBFS3str1P1LS2AL3str1P1L4IMG'S2AL3str1P1L4IMG'2B03H8bFS3str1P1L3H8bS3str1P1L2q02q12DBS3str1P1L2B02q02q13Q012DBFFS3str1P1LS3str1P1L2L0FFFS2AL3str1P1L5ALWF'FFS3str1P1L2B02q02q13Q452DBS3str1P1L2B02q02q12E12DBFFS2AL3str1P1L4IMG'2B02q02q12E03Q01S2AL3str1P1L4IMG'FS2AL3str1P1L4IMG'2B0S2AL3str1P1L4IMG'2B0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma pc_sarg : ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pstr,(2.(3.&8.))PP,$1.Plo,$1.ZL,$1.(8.(9.(3.&8.)R3.))P,(;.$<.R5.R3.(=.(3.&8.)R4.(>.(3.&8.)(?.&8.=)(10.(3.&8.)))))P,(11.(12.(3.&8.)(?.&8.=)R5.))P,(27.$<.VAL,VCS,R7.R5.(14.R3.+1.))P,(15.(14.R4.+1.)(16.+2.+28.))P,(28.R7.(14.(14.(14.R7.R5.)+1.)+7.))P,(13.VCS,(7.R8.(29.R8.+40.))+40.)P,(13.VCS,(7.(14.R9.R7.)(29.(14.R9.R7.)+40.))+40.)P,Pc,$1.P,A1.VCS,R1.(1>.(3.&8.)Lb,(3.&8.)(;.$<.R?.(2:.VAL,R3.)(>.(3.&8.)R1.(10.(3.&8.)))))P,(2;.R=.)P,(26.$<.R>.R;.(23.&40.R2>.))P,(15.+10007???7???.R<.)P,(6.R=.(7.(23.&40.R30.)+50.))P,(13.VCS,R>.(7.(23.&40.R31.)R>.))P,(25.$<.R12.)P,(17.(3.&40.)R1?.(?.&40.R11.))(18.$<.VAL,VCS,(2<.R34.R33.R32.R2>.R2=.R24.R23.R22.R21.R20.R1>.R1=.R1<.R1;.R16.R15.R11.R14.)(1:.(1;.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(?.&40.+5;59<.)R15.(1<.(3.&40.))R14.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. cbn zeta. intros BY NZ OBJ N AR HULL0 HULL1 SHRD RC ST LO0 SPL SCS MI Hs6. al_facts. unfold app_range in AR.
    set (L := Z.of_nat (length str)) in *.
    assert (L0 : 0 <= L) by lia.
    assert (B0 : 0 < P /\ P + L + 1 + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    pose proof (aobj_crange _ _ _ _ _ _ OBJ) as CR.
    (* [comment removed for export] *)
    subst s6. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { eapply (istrlen_loop (length str) 0 str P); try eassumption; try reflexivity; subst L; lia. }
    cbn beta. intros ms1 ->. fold L.
    (* [comment removed for export] *)
    zstep. zstep.
    try (lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]) end).
    zstep. zstep. zstep. rewrite zb_lxor_ones by lia. if_falseU.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    Ltac ripS P L lo :=
      (* [comment removed for export] *)
      zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx P _ |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := P) (n := L + 1) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia | apply f_equal; lia ])
      end;
      (* [comment removed for export] *)
      zstep;
      unfold sarg_post; finish.
    rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec (L + 1) 65) as [SMALL | BIG].
    2:{ replace (L <? 64) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]; cbv iota.
        (* [comment removed for export] *) zstep. if_trueU. ripS P L lo. }
    replace (L <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]; cbv iota.
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m P (L + 1) OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0
                ltac:(replace (P + (L + 1) - 1 - (P + (L + 1) - 1) mod 64) with (P + L - (P + L) mod 64) by (f_equal; [lia | f_equal; lia]); exact HULL1) SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    (* [comment removed for export] *)
    do 11 zstep.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (P + (L + 1) + -1) with (P + (L + 1) - 1) by lia.
    rewrite !Z.mod_small by lia.
    rewrite !land_m8 by lia. rewrite !hull_sh by lia.
    rewrite E0, E1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    { unfold sarg_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (P + (L + 1) - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((P + (L + 1) - 1) / 8) 2147450880) in RDk.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (P / 8) ((P + (L + 1) - 1) / 8)) as [LT|GE].
      - if_falseU. eapply pc_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (P / 8) with ((P + (L + 1) - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a2' & a3' & ->)).
    (* [comment removed for export] *)
    zstep. zstep.
    if_cases Ks.
    { unfold sarg_post; finish. }
    ripS P L lo.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L16405147374.59L26929900252.50L29644601389.59L30095897756.55L35469551417.59L48379326627.59L53520163529.59L53520247005.59L56775215785.59L56775393469.59Q17581378383.58Q35222541774.58Q39502766003.58Q4111067988.58 Q52324771135.5800000C02702D02Z02m03703U04604T05505K05L05\06006JS1k1p1q2lo2Hk2Hp2NES2AL2CS1p1q2ra2sp2gp2tp2t02t12t22s02s12a02a32a42a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo2Hk2HpS1k1p1q2Hk2NES1k1p1q2lo2hi2Hk2Hp2HqS1k1p1q2lo2Hk2Hp2EQS1k1p1q2HkS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2HqFS1k1p1q2lo2Hk2HpS1k1p1q2lo2Hk2Hp3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma mc_orloop : ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Pk,$0.Pp,$1.Pq,$1.Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Plo,$1.Phi,$1.P,(6.(7.R23.R24.)(8.R25.))P,(:.(6.R3.R25.)(15.R25.R24.))P,(6.R25.R3.)P,(15.R4.(16.+2.+3?.))P,(6.=R6.)P,Px,$1.P,(:.(6.R8.R1.)(15.R1.R7.))(1>.(3.&8.)Lb,(3.&8.)(;.$<.R;.R3.(>.(3.&8.)R1.(10.(3.&8.)))))P,Px,$1.P,(:.(6.R9.R1.)(15.R1.R8.))(1?.VAL,VCS,R2.)(18.$<.VAL,VCS,Lms',$19.(1>.(3.&40.)La3',(3.&40.)(1>.(3.&40.)La4',(3.&40.)(17.$19.R3.(1:.(1;.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.(?.&40.R2=.)(?.&40.R2=.)R2.R1.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(?.&40.+5:0:8.)R>.(1<.(3.&40.))R=.(1=.$<.)))))(1:.(1;.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(?.&40.R2;.)(?.&40.R2:.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(?.&40.+5:098.)R;.(1<.(3.&40.))R:.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until hi; intros Hk Hp Hq Hhi Hlo RD AOK; [lia|]. al_facts.
    destruct (RD p ltac:(lia)) as [b B]. pose proof (bytes_at_read1 _ _ _ _ B) as RDB.
    zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec (p + 1) q) as [EQ|NE].
    - if_falseU. rewrite EQ. finish.
    - if_trueU. eapply IH; try eassumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition mc_chk_post (sp gp tp s0 s3 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P L lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Lms',$19.(1>.(3.&40.)Lra',(3.&40.)(1>.(3.&40.)Lt0',(3.&40.)(1>.(3.&40.)Lt1',(3.&40.)(1>.(3.&40.)Lt2',(3.&40.)(1>.(3.&40.)La1',(3.&40.)(1>.(3.&40.)La2',(3.&40.)(1>.(3.&40.)La3',(3.&40.)(1>.(3.&40.)La4',(3.&40.)(1>.(3.&40.)La5',(3.&40.)(1>.(3.&40.)La6',(3.&40.)(1>.(3.&40.)La7',(3.&40.)(1>.(3.&40.)Ls2',(3.&40.)(1>.(3.&40.)Ls4',(3.&40.)(1>.(3.&40.)Ls5',(3.&40.)(1>.(3.&40.)Lt3',(3.&40.)(1>.(3.&40.)Lt4',(3.&40.)(1>.(3.&40.)Lt5',(3.&40.)(1>.(3.&40.)Lt6',(3.&40.)(1>.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(:.(17.$19.R14.(1:.(1;.R13.O11.O10.O?.R12.R11.R10.O>.(?.&40.(14.O3.+1.))(?.&40.(14.O4.O3.))R?.R>.R=.R<.R;.R:.R9.R8.O=.R7.R6.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(?.&40.+59?88.)O5.(1<.(3.&40.))R1.(1=.$<.)))(:.(20.(>.(21.$1.$1.)(22.$1.$1.O2.(23.&40.O11.))(10.(21.$1.$1.)))O1.R1.)(:.(24.$<.O1.R1.)(:.(25.$<.R1.)(26.$<.R1.O2.(23.&40.O11.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0260@C17025492443.112C17025492443.90 L11447729323.150L11671109536.85 L11944109973.87 L13946194139.93 L13948180391.71 L17423148388.91 L17820268298.71 L1952302740.86  L1956330362.71  L19628431903.89 L19885240167.71 L20966712717.91 L21816074906.71 L22721961905.71 L22774446881.0  L24122754266.91 L24122936649.91 L24124928684.85 L24124928684.86 L24982526223.89 L25727469113.57 L28083348026.87 L2810144006.86  L28552145834.71 L29784464483.90 L29786564236.86 L31686803170.91 L31913121063.71 L3248729870.2   L33139774177.91 L3421674955.91  L34922678286.2  L36929494798.2  L37862823410.93 L37865032334.71 L38150352304.91 L39594679749.86 L40387107599.71 L45165531934.86 L45607281678.2  L47543971773.91 L49899794702.2  L50296483778.91 L5054181744.70  L51172192526.2  L52065394884.85 L52514161039.89 L53517158443.71 L53519158063.89 L61097676998.2  L66488557582.2  L7106453518.2   O14206727921.112O14206727921.90 O15547502833.112O15547502833.90 O17025492443.112O17025492443.90 O23485702385.112O23485702385.90 O32131581681.112O32131581681.90 O38504098033.112O38504098033.90 O4492316913.112 O4492316913.90  O48978854641.112O48978854641.90 O65485481713.112O65485481713.90 P3245129067.112 P3245129067.90  P34917767787.112P34917767787.90 P36941614443.112P36941614443.90 P45611546219.112P45611546219.90 P49904706411.112P49904706411.90 P51184575339.112P51184575339.90 P66501341803.112P66501341803.90 P7102853739.112 P7102853739.90  Q12781370905.87 Q14673372720.86 Q15643823314.86 Q16263154483.86 Q19275945964.86 Q21773766844.86 Q21797814763.86 Q24745328269.90 Q26151546087.90 Q28218390483.90 Q29427030349.86 Q30057916957.86 Q31394395900.86 Q34268098539.86 Q34501421650.86 Q36722057835.86 Q38148316102.86 Q39778974580.86 Q39942779359.86 Q41324687698.90 Q43608312681.87 Q43855177782.86 Q44556843737.90 Q45514747608.86 Q45748806138.90 Q46309744770.90 Q46311840365.86 Q47282368501.86 Q47312252080.86 Q51241282684.86 Q51260952339.87 Q52818999351.86 Q52821082840.90 Q53500367258.86 Q53519998161.86 Q54173355287.86 Q57150186488.90 Q59322611797.86 Q59365683033.86 Q61975411717.90 Q62698369181.86 Q62824840384.86 Q63037122486.86 Q6460837458.86  Q66715486460.86 Q67805910652.86 00000100200300>00?00I00Q00Y00a00i01101<01C01O01X01]01^01k02802902F02K02S02T02_02e02j02o03=03E03F03N03_03`03a03i04104F04S04_04d04e05305405E05M05N05Y05^05_05d05e05f05g05h05i05j05k06606A06B06C06D06E06F06G06H06I06J06K06L06M06\06g07607A07P07[07j08508D08O08^08i09809C09R09]09b09c09d09e0:10:20:30:G0:H0:Q0:R0:S0:X0;00;10;20;G0;O0;k0;l0<10<>0<R0<S0<\0<j0=B0=C0=D0=I0=Q0=R0=S0=T0=b0=c0=d0>90>M0>N0>O0>l0?90?:0?J0?ZFFFS1P1L2L02B0FS1P1L2L01NS1L2L01NS1P1L2LTS1P1L2B0S1P1L2B0S1P1L2B0S1P1L2L02B0S1L3BIGS1P1L2q13Q45S1L5SMALLS1P1LSS1P1L3H8a3H8bS1P1L3H8a3H8bFS1P1L3H8b3H8aS1P1LS1P1L2ARFS1P1L2L02B0S1L2L0S1P1LS1P1LS1P1L2q02q12DBS1L2L01NFS1P1L2GES1P1L2q02q12DB2LTFFS1P1L2ARS1P1L2ARS1P1L2B02q02q12E03Q01S1P1L3H8b3H8aS1L2L05SMALLS1P1LFS1P1L2B05SMALLFS1P1L2q02q12DB2GES1L2L01NFS1P1L2L02B0S1P1LSS1P1LFFFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S1P1LFFFS1P1L2q13Q45FFS1P1L2L02B02q02q12DBFS1P1L3H8bFFS1P1LS1P1L2L02B02q02q13Q012DBFFS1P1L2B02q02q12E03Q01S1P1L2q0S2AL1P1L4IMG'2B02q02q12E12DBFS1P1LS2AL1P1L4IMG'S2AL1P1L4IMG'2B03H8bFS1P1L3H8bS1P1L2q02q12DBS1P1L2L02B02q02q13Q012DBFFS1P1LS1P1L2L0FFFS2AL1P1L5ALWF'FFS1P1L2B02q02q13Q452DBS1P1L2B02q02q12E12DBFFS2AL1P1L4IMG'2B02q02q12E03Q01S2AL1P1L4IMG'FS2AL1P1L4IMG'2B0S2AL1P1L4IMG'2B0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma mc_chk : ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))PP,$1.PL,$1.Plo,$1.P,(27.$<.VAL,VCS,R4.R3.(14.R2.+1.))P,(6.=R3.)P,(15.(14.R4.+1.)(16.+2.+28.))P,(28.R6.(14.(14.(14.R6.R5.)+1.)+7.))P,(13.VCS,(7.R7.(29.R7.+40.))+40.)P,(13.VCS,(7.(14.R8.R7.)(29.(14.R8.R7.)+40.))+40.)P,Pc,$1.P,A1.VCS,R1.(1>.(3.&8.)Lb,(3.&8.)(;.$<.R=.(2:.VAL,R3.)(>.(3.&8.)R1.(10.(3.&8.)))))P,(2;.R;.)P,(26.$<.R<.R9.(23.&40.R29.))P,(15.+10007???7???.R:.)P,(6.R;.(7.(23.&40.R2;.)+50.))P,(13.VCS,R<.(7.(23.&40.R2<.)R<.))P,(25.$<.R10.)(18.$<.VAL,VCS,(2=.R2>.R2=.R2<.R28.R20.R1=.R1<.R1;.R1:.R19.R18.R13.R12.R10.R?.R>.R11.)(1:.(1;.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(?.&40.(14.R?.+1.))(?.&40.(14.R10.R?.))R27.R26.R25.R24.R23.R22.R21.(?.&40.R10.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(?.&40.+59?40.)R12.(1<.(3.&40.))R11.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ L0 N AR HULL0 HULL1 SHRD RC ST LO0 SPL SCS MI. al_facts. unfold app_range in AR.
    assert (B0 : 0 < P /\ P + L + 1 + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    pose proof (aobj_crange _ _ _ _ _ _ OBJ) as CR.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    Ltac ripMC P L lo :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx P _ |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := P) (n := L + 1) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia | apply f_equal; lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep;
      unfold mc_chk_post; finish.
    rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec (L + 1) 65) as [SMALL | BIG].
    2:{ replace (L <? 64) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]; cbv iota.
        (* [comment removed for export] *) zstep. if_trueU. ripMC P L lo. }
    replace (L <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]; cbv iota.
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m P (L + 1) OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0
                ltac:(replace (P + (L + 1) - 1 - (P + (L + 1) - 1) mod 64) with (P + L - (P + L) mod 64) by (f_equal; [lia | f_equal; lia]); exact HULL1) SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    (* [comment removed for export] *)
    do 11 zstep.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (P + (L + 1) + -1) with (P + (L + 1) - 1) by lia.
    rewrite !Z.mod_small by lia.
    rewrite !land_m8 by lia. rewrite !hull_sh by lia.
    rewrite E0, E1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold mc_chk_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (P + (L + 1) - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((P + (L + 1) - 1) / 8) 2147450880) in RDk.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (P / 8) ((P + (L + 1) - 1) / 8)) as [LT|GE].
      - if_falseU. eapply mc_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (P / 8) with ((P + (L + 1) - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3'' & a4'' & ->)).
    (* [comment removed for export] *)
    zstep. zstep.
    if_cases Ks.
    { unfold mc_chk_post; finish. }
    ripMC P L lo.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L16405147374.59L29644601389.59L30095897756.55L35469551417.59L48379326627.59L48562921628.50L53520163529.59L53520247005.59L56775215785.59L56775393469.59Q17581378383.58Q35222541774.58Q39502766003.58Q4111067988.58 Q52324771135.5800000C00P00f01901C03703U04604T05505K05L05\06006JS1k1p1q2lo2Hk2Hp2NES1k1p1q2Hk2NES1k1p1q2lo2hi2Hk2Hp2HqS1k1p1q2lo2Hk2Hp2EQS1k1p1q2HkS2AL2CS1p1q2ra2sp2gp2tp2t02t12t22s02s12a02a32a42a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo2Hk2HpS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2HqFS1k1p1q2lo2Hk2HpS1k1p1q2lo2Hk2Hp3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma sn_orloop : ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Pk,$0.Pp,$1.Pq,$1.Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Plo,$1.Phi,$1.P,(6.(7.R23.R24.)(8.R25.))P,(:.(6.R3.R25.)(15.R25.R24.))P,(6.R25.R3.)P,(15.R4.(16.+2.+3?.))P,(6.=R6.)P,Px,$1.P,(:.(6.R8.R1.)(15.R1.R7.))(1>.(3.&8.)Lb,(3.&8.)(;.$<.R;.R3.(>.(3.&8.)R1.(10.(3.&8.)))))P,Px,$1.P,(:.(6.R9.R1.)(15.R1.R8.))(1?.VAL,VCS,R2.)(18.$<.VAL,VCS,Lms',$19.(1>.(3.&40.)La3',(3.&40.)(1>.(3.&40.)La4',(3.&40.)(17.$19.R3.(1:.(1;.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.(?.&40.R2=.)(?.&40.R2=.)R2.R1.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(?.&40.+58;;<.)R>.(1<.(3.&40.))R=.(1=.$<.)))))(1:.(1;.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(?.&40.R2;.)(?.&40.R2:.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(?.&40.+58;:<.)R;.(1<.(3.&40.))R:.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until hi; intros Hk Hp Hq Hhi Hlo RD AOK; [lia|]. al_facts.
    destruct (RD p ltac:(lia)) as [b B]. pose proof (bytes_at_read1 _ _ _ _ B) as RDB.
    zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec (p + 1) q) as [EQ|NE].
    - if_falseU. rewrite EQ. finish.
    - if_trueU. eapply IH; try eassumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition sn_chk_post (sp gp tp s0 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P L lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Lms',$19.(1>.(3.&40.)Lra',(3.&40.)(1>.(3.&40.)Lt0',(3.&40.)(1>.(3.&40.)Lt1',(3.&40.)(1>.(3.&40.)Lt2',(3.&40.)(1>.(3.&40.)La1',(3.&40.)(1>.(3.&40.)La2',(3.&40.)(1>.(3.&40.)La3',(3.&40.)(1>.(3.&40.)La4',(3.&40.)(1>.(3.&40.)La5',(3.&40.)(1>.(3.&40.)La6',(3.&40.)(1>.(3.&40.)La7',(3.&40.)(1>.(3.&40.)Ls2',(3.&40.)(1>.(3.&40.)Ls4',(3.&40.)(1>.(3.&40.)Ls6',(3.&40.)(1>.(3.&40.)Lt3',(3.&40.)(1>.(3.&40.)Lt4',(3.&40.)(1>.(3.&40.)Lt5',(3.&40.)(1>.(3.&40.)Lt6',(3.&40.)(1>.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(:.(17.$19.R14.(1:.(1;.R13.O11.O10.O?.R12.R11.R10.O>.(?.&40.(14.O3.+1.))(?.&40.O3.)R?.R>.R=.R<.R;.R:.R9.R8.O=.R7.O<.R6.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(?.&40.+58:=8.)O5.(1<.(3.&40.))R1.(1=.$<.)))(:.(20.(>.(21.$1.$1.)(22.$1.$1.O2.(23.&40.O11.))(10.(21.$1.$1.)))O1.R1.)(:.(24.$<.O1.R1.)(:.(25.$<.R1.)(26.$<.R1.O2.(23.&40.O11.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02;0@C17025492443.112C17025492443.90 L11447729323.150L11668818640.69 L11668818640.70 L11671109536.85 L11944109973.87 L13946194139.93 L13948180391.71 L17423148388.91 L17820268298.71 L1952302740.86  L1956330362.71  L19628431903.89 L19885240167.71 L20966712717.91 L21816074906.71 L22721961905.71 L2354636449.0   L24122754266.91 L24122936649.91 L24124928684.85 L24124928684.86 L24982526223.89 L25727469113.57 L28083348026.87 L2810144006.86  L28552145834.71 L29784464483.90 L29786564236.86 L30124523164.70 L31686803170.91 L31911041468.70 L31913121063.71 L3248729870.2   L33139774177.91 L3421674955.91  L34922678286.2  L36929494798.2  L37862823410.93 L37865032334.71 L38150352304.91 L39594679749.86 L40387107599.71 L45165531934.86 L45607281678.2  L47543971773.91 L49899794702.2  L50296483778.91 L5054181744.70  L51172192526.2  L52065394884.85 L52514161039.89 L53517158443.71 L53519158063.89 L61097676998.2  L63950803142.70 L66488557582.2  L7106453518.2   O14206727921.112O14206727921.90 O15547502833.112O15547502833.90 O17025492443.112O17025492443.90 O23485702385.112O23485702385.90 O32131581681.112O32131581681.90 O38504098033.112O38504098033.90 O4492316913.112 O4492316913.90  O48978854641.112O48978854641.90 O65485481713.112O65485481713.90 P3245129067.112 P3245129067.90  P34917767787.112P34917767787.90 P36941614443.112P36941614443.90 P45611546219.112P45611546219.90 P49904706411.112P49904706411.90 P51184575339.112P51184575339.90 P66501341803.112P66501341803.90 P7102853739.112 P7102853739.90  Q12781370905.87 Q14673372720.86 Q15643823314.86 Q16263154483.86 Q19275945964.86 Q21773766844.86 Q21797814763.86 Q24745328269.90 Q26151546087.90 Q28218390483.90 Q29427030349.86 Q30057916957.86 Q31394395900.86 Q34268098539.86 Q34501421650.86 Q36722057835.86 Q38148316102.86 Q39778974580.86 Q39942779359.86 Q41324687698.90 Q43608312681.87 Q43855177782.86 Q44556843737.90 Q45514747608.86 Q45748806138.90 Q46309744770.90 Q46311840365.86 Q47282368501.86 Q47312252080.86 Q51241282684.86 Q51260952339.87 Q52818999351.86 Q52821082840.90 Q53500367258.86 Q53519998161.86 Q54173355287.86 Q57150186488.90 Q59322611797.86 Q59365683033.86 Q61975411717.90 Q62698369181.86 Q62824840384.86 Q63037122486.86 Q6460837458.86  Q66715486460.86 Q67805910652.86 00000100200300>00I00T00U00_00g00o01701?01G01R01Y01e01n02302402A02N02O02\02a02i02j03503;03@03E03P03^03f03n03o04704H04I04J04R04Z04o05<05H05M05N05\05]05n06606706B06G06H06M06N06V06W06X06Y06Z06[06\06g07207307407507607707807907:07;07<07=07>07M07X07g08208A08L08[08f09509@09O09Z09i0:40:C0:N0:S0:T0:U0:V0:b0:c0:d0;80;90;B0;C0;D0;I0;a0;b0;c0<80<@0<\0<]0<b0<o0=C0=D0=M0=[0>30>40>50>:0>B0>C0>D0>E0>S0>T0>U0>j0?>0??0?@0?]0?j0?k0@;0@KFFFS1P1L2L02B0S1P1L2L02B0S1P1L2L02B0FS1P1L2L01NS1L2L01NS1P1L2LTS1P1L2B0S1P1L2B0S1P1L2B0S1P1L2L02B0S1L3BIGS1P1L2q13Q45S1L5SMALLS1P1LSS1P1L3H8a3H8bS1P1L3H8a3H8bFS1P1L3H8b3H8aS1P1LS1P1L2ARFS1P1L2L02B0S1L2L0S1P1LS1P1LS1P1L2L02B0S1P1L2q02q12DBS1L2L01NS1L2L01NFS1P1L2GES1P1L2q02q12DB2LTFFS1P1L2ARS1P1L2ARS1P1L2B02q02q12E03Q01S1P1L3H8b3H8aS1L2L05SMALLS1P1LFS1P1L2B05SMALLFS1P1L2q02q12DB2GES1L2L01NFS1P1L2L02B0S1P1LSS1P1LFS1P1L2B0FFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S2sp1P1L2lo3LO0S2sp2lo3LO0S1P1LFFFS1P1L2q13Q45FFS1P1L2L02B02q02q12DBFS1P1L3H8bFFS1P1LS1P1L2L02B02q02q13Q012DBFFS1P1L2B02q02q12E03Q01S1P1L2q0S2AL1P1L4IMG'2B02q02q12E12DBFS1P1LS2AL1P1L4IMG'S2AL1P1L4IMG'2B03H8bFS1P1L3H8bS1P1L2q02q12DBS1P1L2L02B02q02q13Q012DBFFS1P1LS1P1L2L0FFFS2AL1P1L5ALWF'FFS1P1L2B02q02q13Q452DBS1P1L2B02q02q12E12DBFFS2AL1P1L4IMG'2B02q02q12E03Q01S2AL1P1L4IMG'FS2AL1P1L4IMG'2B0S2AL1P1L4IMG'2B0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma sn_chk : ltac2:(CDefT.buildp (gd_tbl_A_icpt_str ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))PP,$1.PL,$1.Plo,$1.P,(27.$<.VAL,VCS,R4.R3.(14.R2.+1.))P,(6.=R3.)P,(15.(14.R4.+1.)(16.+2.+28.))P,(28.R6.(14.(14.(14.R6.R5.)+1.)+7.))P,(13.VCS,(7.R7.(29.R7.+40.))+40.)P,(13.VCS,(7.(14.R8.R7.)(29.(14.R8.R7.)+40.))+40.)P,Pc,$1.P,A1.VCS,R1.(1>.(3.&8.)Lb,(3.&8.)(;.$<.R=.(2:.VAL,R3.)(>.(3.&8.)R1.(10.(3.&8.)))))P,(2;.R;.)P,(26.$<.R<.R9.(23.&40.R29.))P,(15.+10007???7???.R:.)P,(6.R;.(7.(23.&40.R2;.)+50.))P,(13.VCS,R<.(7.(23.&40.R2<.)R<.))P,(25.$<.R10.)(18.$<.VAL,VCS,(2>.R2>.R2=.R2<.R28.R20.R1>.R1<.R1;.R1:.R19.R18.R13.R12.R10.R?.R>.R11.)(1:.(1;.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(?.&40.(14.R?.+1.))(?.&40.R?.)R27.R26.R25.R24.R23.R22.R21.(?.&40.R10.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(?.&40.+58:80.)R12.(1<.(3.&40.))R11.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ L0 N AR HULL0 HULL1 SHRD RC ST LO0 SPL SCS MI. al_facts. unfold app_range in AR.
    assert (B0 : 0 < P /\ P + L + 1 + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    pose proof (aobj_crange _ _ _ _ _ _ OBJ) as CR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite zb_lxor_ones by lia. if_falseU.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    Ltac ripSN P L lo :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx P _ |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := P) (n := L + 1) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia | apply f_equal; lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep;
      unfold sn_chk_post; finish.
    rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec (L + 1) 65) as [SMALL | BIG].
    2:{ replace (L <? 64) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]; cbv iota.
        (* [comment removed for export] *) zstep. if_trueU. ripSN P L lo. }
    replace (L <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]; cbv iota.
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m P (L + 1) OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0
                ltac:(replace (P + (L + 1) - 1 - (P + (L + 1) - 1) mod 64) with (P + L - (P + L) mod 64) by (f_equal; [lia | f_equal; lia]); exact HULL1) SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    (* [comment removed for export] *)
    do 11 zstep.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (P + (L + 1) + -1) with (P + (L + 1) - 1) by lia.
    rewrite !Z.mod_small by lia.
    rewrite !land_m8 by lia. rewrite !hull_sh by lia.
    rewrite E0, E1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold sn_chk_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (P + (L + 1) - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((P + (L + 1) - 1) / 8) 2147450880) in RDk.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (P / 8) ((P + (L + 1) - 1) / 8)) as [LT|GE].
      - if_falseU. eapply sn_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (P / 8) with ((P + (L + 1) - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3'' & a4'' & ->)).
    (* [comment removed for export] *)
    zstep. zstep.
    if_cases Ks.
    { unfold sn_chk_post; finish. }
    ripSN P L lo.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

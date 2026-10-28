(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells CellsX Step Frame HeapIface Asn1Aux MpiWalkAux Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts CrtExtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_crt_parse.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_ext_area.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_A_x509_crt_parse_area () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_parse.wbuf"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.crt_own_ok"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_parse.f_of"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_parse.jraw"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_own"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_junk"; "Area.chunks"; "Area.owns"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.CRT_SIZE"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.crt_junk"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.crt_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.crt_zero"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.zeros"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_own_zero"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_junk_zero"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"].


Section Area.
  Variable segs : list Segment.
  Variable PK : pk_class segs.

  Definition chunks (mc : mem) (A : Z)
      (ob h1 h2 h3 : word) (rawlen rawp : Z)
      (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte)
      (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z)
      (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_area ()) "(0.(1.Vsegs,O3>.O3=.(2.$3.(4.O3<.)(2.$3.(4.O3;.)(2.$3.(4.O3:.)(2.$3.(4.O39.)(2.$3.(5.(6.&40.O38.))(2.$3.(5.(6.&40.O37.))(7.$3.))))))))(0.(1.Vsegs,O3>.(8.O3=.+20.)(2.$3.(4.O36.)(2.$3.(4.O35.)(2.$3.(5.O34.)(2.$3.(5.O33.)(2.$3.(4.O32.)(2.$3.(4.O31.)(7.$3.))))))))(0.(1.Vsegs,O3>.(8.O3=.+40.)(9.O30.O2?.O2>.O2=.))(0.(1.Vsegs,O3>.(8.O3=.+58.)(:.O2<.O2;.O2:.O29.))(0.(1.Vsegs,O3>.(8.O3=.+70.)(:.O28.O27.O26.O25.))(0.(1.Vsegs,O3>.(8.O3=.+88.)(:.O24.O23.O22.O21.))(0.(1.Vsegs,O3>.(8.O3=.+:0.)(;.O20.O1?.O1>.O1=.))(0.(1.Vsegs,O3>.(8.O3=.+>0.)(;.O1<.O1;.O1:.O19.))(0.(1.Vsegs,O3>.(8.O3=.+120.)(2.$3.(<.#30.O18.)(7.$3.)))(0.(1.Vsegs,O3>.(8.O3=.+150.)(:.O17.O16.O15.O14.))(0.(1.Vsegs,O3>.(8.O3=.+168.)(2.$3.(5.(6.&40.O13.))(2.$3.(5.(6.&40.O12.))(7.$3.))))(0.(1.Vsegs,O3>.(8.O3=.+178.)(:.O11.O10.O?.O>.))(0.(1.Vsegs,O3>.(8.O3=.+190.)(:.O=.O<.O;.O:.))(0.(1.Vsegs,O3>.(8.O3=.+1:8.)(=.O9.O8.))(0.(1.Vsegs,O3>.(8.O3=.+2;8.)(9.O7.O6.O5.O4.))(1.Vsegs,O3>.(8.O3=.+2=0.)(2.$3.(4.O3.)(2.$3.(4.O2.)(2.$3.(5.(6.&40.O1.))(2.$3.(5.(6.&40.=))(7.$3.)))))))))))))))))))))")
(* [comment removed for export] *).

  Definition owns (mc : mem) (LBx : list blk) (A : Z) (ob : word) (rawlen rawp inext : Z) (inodes : list Z) (snext : Z) (snodes : list Z)
      (pkinfo pkctx : Z) (pkowned : list blk) (eo : ext_own) (sigopts : Z) (rawjunk : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_area ()) "(>.Vsegs,VPK,O10.O?.O>.(?.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.)(10.O1.))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L10138756247.89L14059206295.79L26029608087.78L32895936663.80L35883376279.81L4106130583.88 L42805251223.86L43951481239.83L50714970519.82L51397467799.90L55916688279.84L58624325271.87L61641067630.76L63630015639.85L7183725975.77 00000300600900<00?00B00E00H00K00N00Q00T00W00Z00]S1AS1AS1AS1AS1AS1AS1AS1AS1AS1AS1AS1AS1AS1AS1A". (* [comment removed for export] *)
  #[using="Type"] Lemma crt_at_build : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_area ()) "Pmc,P,(11.&40.)(12.(11.&8.))PLBx,(13.$14.)PA,$15.Pob,(11.&40.)Ph1,(11.&40.)Ph2,(11.&40.)Ph3,(11.&40.)Prawlen,$15.Prawp,$15.Ptbt,(11.&40.)Ptbd,(11.&40.)Ptbl,(11.&40.)Ptbp,(11.&40.)Pver,(11.&40.)Pverpad,(11.&40.)Pstg,(11.&40.)Pspd,(11.&40.)Pslen,$15.Psq,$15.Pso1,(11.&40.)Pso2,(11.&40.)Pso3,(11.&40.)Pso4,(11.&40.)Pir1,(11.&40.)Pir2,(11.&40.)Pir3,(11.&40.)Pir4,(11.&40.)Psr1,(11.&40.)Psr2,(11.&40.)Psr3,(11.&40.)Psr4,(11.&40.)Pij48,(13.(11.&8.))Pinext,$15.Pimg,(11.&8.)Pipad,(13.(11.&8.))Psj48,(13.(11.&8.))Psnext,$15.Psmg,(11.&8.)Pspad,(13.(11.&8.))Pdates,(13.(11.&8.))Ppr1,(11.&40.)Ppr2,(11.&40.)Ppr3,(11.&40.)Ppr4,(11.&40.)Ppkinfo,$15.Ppkctx,$15.Pu1,(11.&40.)Pu2,(11.&40.)Pu3,(11.&40.)Pu4,(11.&40.)Pv1,(11.&40.)Pv2,(11.&40.)Pv3,(11.&40.)Pv4,(11.&40.)Peo,$16.Pej,$17.Pgtg,(11.&40.)Pgpd,(11.&40.)Pglen,$15.Pgq,$15.Psigmd,(11.&40.)Psigpk,(11.&40.)Psigopts,$15.Pinodes,(13.$15.)Psnodes,(13.$15.)Prawjunk,(13.(11.&8.))Ppkowned,(13.$14.)P,(18.R43.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(19.R44.R43.R42.R41.R3=.R3<.R24.R5.R20.R4.R18.R17.R2.R>.R6.R3.)P,(1:.$15.(1;.R43.+8.)=)P,(1<.=R44.)P,(1=.(8.R45.$1>.)(1?.+2.+40.))(20.$21.Lj,$21.(22.Vsegs,VPK,R49.R48.R47.(?.R46.R42.R41.R29.R:.R25.R9.R1=.R1<.R7.R13.R;.)R1.))")
(* [comment removed for export] *).
  Proof.
    intros mc LBx A ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej
           gtg gpd glen gq sigmd sigpk sigopts inodes snodes rawjunk pkowned
           CH OW HAL HA AB.
    ddestruct CH as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
    Ltac jn H1 H2 :=
      lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
      lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
        let v := eval vm_compute in (Z.of_nat (cells_size cs1)) in
        let Hj := fresh "J" in
        pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2)) as Hj;
        let He := fresh "E" in
        assert (He : Z.of_nat (cells_size cs1) = v) by reflexivity; rewrite He in Hj; clear He;
        replace A2 with (A1 + v) in H2 by lia;
        specialize (Hj (conj H1 H2)); clear H1 H2; rename Hj into H1
      end end.
    unfold wbuf, buf_cells, name_blob, ext_cells in *.
    jn K14 K15. jn K13 K14. jn K12 K13. jn K11 K12. jn K10 K11. jn K9 K10. jn K8 K9. jn K7 K8. jn K6 K7.
    jn K5 K6. jn K4 K5. jn K3 K4. jn K2 K3. jn K1 K2. jn K0 K1. cbn [app] in K0.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac spine_firstn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
      | Datatypes.S ?k' => lazymatch cs with
                 | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
                 | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
                 end
      end.
    Ltac spine_skipn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => cs
      | Datatypes.S ?k' => lazymatch cs with
                 | _ :: ?cs' => spine_skipn k' cs'
                 | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
                 end
      end.
    Ltac mergeat H i k :=
      lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
        let pre := spine_firstn i cs in
        let mid := (let spt := spine_skipn i cs in spine_firstn k spt) in
        let post := spine_skipn (i + k)%nat cs in
        change (rw_cells sg mm A0 (pre ++ mid ++ post)) in H;
        apply rw_cells_merge in H; cbn [cells_size csize Nat.add app] in H
      end.
    (* [comment removed for export] *)
    mergeat K0 59%nat 7%nat.     (* [comment removed for export] *)
    mergeat K0 43%nat 9%nat.     (* [comment removed for export] *)
    mergeat K0 34%nat 7%nat.     (* [comment removed for export] *)
    mergeat K0 30%nat 3%nat.     (* [comment removed for export] *)
    mergeat K0 6%nat 23%nat.     (* [comment removed for export] *)
    eexists (CRJ h1 h2 h3 _ _ _ _ (ej1 ej) (ej2 ej) (ej3 ej) _ rawjunk).
    split; [| split; [exact HAL| split; [exact HA| split; [exact AB|]]]].
    - unfold crt_cells, f_of. cbn [co_ob co_rawlen co_rawp co_issuer_next co_subject_next co_pkinfo co_pkctx co_san_next co_akid_next co_pol_next co_eku_next co_sigopts
                             co_issuer co_subject co_pkowned co_san co_akid co_pol co_eku
                             cj0 cj_rawtag cj1 cj2 cj3 cj4 cj5 cj6 cj7 cj8 cj9].
      exact K0.
    - exact OW.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section Zero.
  Variable CRT : Z.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L25274087060.5000001S". (* [comment removed for export] *)
    #[using="Type"] Lemma chunks_of_zero : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_area ()) "Pmq,P,(11.&40.)(12.(11.&8.))P,(23.Vsegs,R1.VCRT,)(18.R2.VCRT,(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)==(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)==(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(24.#30.)=(6.&8.=)(24.#7.)(24.#30.)=(6.&8.=)(24.#7.)(24.#30.)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)==(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)(6.&40.=)$25.$26.(6.&40.=)(6.&40.=)==(6.&40.=)(6.&40.=)=)")
(* [comment removed for export] *).
    Proof.
      intros mq CZq. unfold crt_zero in CZq. unfold chunks, wbuf, buf_cells, name_blob, ext_cells, ext_own_zero, ext_junk_zero.
      cbn [eo_san_next eo_akid_next eo_pol_next eo_eku_next ej0 ej1 ej2 ej3 ej4].
      Ltac zs CZq off := first [ replace CRT with (CRT + Z.of_nat 0) by lia; eapply (zero_sub segs _ _ _ 0); [exact CZq| cbn; repeat split; reflexivity| cbn; lia]
                              | eapply (zero_sub segs _ _ _ off); [exact CZq| cbn; repeat split; reflexivity| cbn; lia] ].
      repeat match goal with |- _ /\ _ => split end.
      1: pose proof (zero_sub segs mq CRT 744 0 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] CZq ltac:(cbn; repeat split; reflexivity) ltac:(cbn; lia)) as H;
         rewrite Z.add_0_r in H; exact H.
      all: lazymatch goal with |- rw_cells _ _ (CRT + ?off) ?cs =>
             let offn := eval vm_compute in (Z.to_nat off) in
             pose proof (zero_sub segs mq CRT 744 offn cs CZq ltac:(cbn; repeat split; reflexivity) ltac:(cbn; lia)) as H;
             let v := eval vm_compute in (Z.of_nat offn) in change (Z.of_nat offn) with v in H; exact H end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    #[using="Type"] Lemma owns_zero : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_area ()) "Pmq,P,(11.&40.)(12.(11.&8.))PLBq,(13.$14.)Ph0,(11.&40.)Ph00,(11.&40.)(19.R4.R3.VCRT,(6.&40.=)===(7.$15.)=(7.$15.)==(7.$14.)$25.=(7.(11.&8.)))")
(* [comment removed for export] *).
    Proof. intros. unfold owns. exact (crt_own_ok_zero segs PK mq LBq CRT). Qed.

    (* [comment removed for export] *)
  End Zero.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L14625388027.24L9839182322.20 00000I00oS6rawlen7rawjunk4HLEN3HwfS4segs2mc3LBx6rawlen4rawp7rawjunk1E2RP". (* [comment removed for export] *)
  #[using="Type"] Lemma raw_facts : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_area ()) "Pmc,P,(11.&40.)(12.(11.&8.))PLBx,(13.$14.)PCRT,$15.Pob,(11.&40.)Prawlen,$15.Prawp,$15.Pinext,$15.Pinodes,(13.$15.)Psnext,$15.Psnodes,(13.$15.)Ppkinfo,$15.Ppkctx,$15.Ppkowned,(13.$14.)Peo,$16.Psigopts,$15.Prawjunk,(13.(11.&8.))P,(19.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(1<.=R<.)(0.(27.Vsegs,R12.R=.R3.)(0.(1:.$15.(28.(29.(11.&8.)R3.))R>.)(0.(2:.(2;.$15.$15.)(2<.$15.$15.R=.R>.)R11.)(1=.=R>.))))")
(* [comment removed for export] *).
  Proof.
    intros mc LBx CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk OW RP.
    unfold owns, crt_own_ok, f_of, jraw in OW. cbn [co_rawp co_rawlen cj_raw] in OW.
    ddestruct OW as (_ & _ & _ & _ & _ & _ & _ & RAW & _). destruct RAW as [E|(HIN & HLEN & RC)]; [lia|].
    pose proof RC as RC'. destruct RC' as [[Hwf Hb] _]. cbn in Hwf. destruct Hwf as [Hwf _].
    split; [| split; [lia| split; [exact HIN| exact HLEN]]].
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Area.

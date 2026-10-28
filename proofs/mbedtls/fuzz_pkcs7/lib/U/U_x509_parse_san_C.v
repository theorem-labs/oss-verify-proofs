(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_oid U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_get_name U_x509_parse_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1 LxU_SumsHeapO.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001bbe265b24288c 0 2 0 1 25 1P00e1ed795e3e241b 1 1 8 3 0 1 47 1 48 1 6 2 2 31 2 39 2 46 2 49 2 50 16P00fbd9c7042ef831 0 3 0 1 5 1 36 1P0221b468e9e43b73 1 1 8 3 1 1 47 1 48 1 6 2 2 31 2 39 2 46 2 49 2 50 16P0267a81efc3f7ed1 0 2 0 1 27 1P044d9d4802dbf45c 0 6 1 1 2 1 22 1 30 1 37 1 38 1P04dde185eff8a04d 1 1 8 3 1 1 38 1 39 1 4 2 2 37 2 40 2 41 16P0639411e7ec45748 0 4 0 1 2 1 48 1 49 1P0652e90171ff6ee0 0 6 1 1 2 1 31 1 39 1 46 1 47 1P074f39e06b3d6253 2 16 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P080309a6fa2b5b1c 0 4 0 1 2 1 46 1 47 1P0856b5c3912e9dad 1 1 8 3 1 1 47 1 48 1 6 2 2 31 2 39 2 46 2 49 2 50 16P087f8f22438eec9c 1 1 8 3 0 1 38 1 39 1 6 2 2 22 2 30 2 37 2 40 2 41 16P092f2873626c4716 0 4 0 1 26 1 44 1 45 1P0a72ead2ea443a65 1 1 8 3 0 1 46 1 49 1 4 2 2 47 2 48 2 50 16P0adb1bea3a596749 0 5 0 1 20 1 28 1 35 1 36 1P0b9509e83b1284b6 0 1 1 1P0c769f8d93b8e09e 0 2 0 1 26 1P0e31ac086312fe0e 0 4 0 8 18 8 44 8 45 8P0ef1b339b1081358 0 6 1 1 3 1 23 1 31 1 38 1 39 1P0f152e534ccae6ae 0 4 0 1 2 1 39 1 40 1P0f340707bc49275b 0 2 0 1 28 1P0f3fbfb71a6bff81 0 2 0 1 4 1P0f70c92314c8b13d 0 2 0 1 3 1P1139d02c1f7bb380 0 2 0 1 30 1P11dfa1d3dc50dfff 0 6 1 1 2 1 22 1 30 1 37 1 38 1P137955fed27e876c 0 1 1 1P144a812c5c2c165d 0 4 0 1 3 1 38 1 39 1P15ea4106a9f86d21 0 5 0 1 21 1 29 1 40 1 41 1P1656f46c26214df1 1 1 8 3 0 1 37 1 40 1 4 2 2 38 2 39 2 41 16P176058f7051df039 2 17 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P186599bcbe4f497a 0 2 0 1 24 1P1bb72236ba5f6506 0 4 0 1 29 1 44 1 45 1P1bd8f36c7abe3f3c 0 2 0 1 5 1P1bdd79c1cfd42ee7 0 2 0 1 2 1P1c3cef49fb0c1acf 0 5 0 1 20 1 28 1 35 1 36 1P1c570c9decb15ba1 0 2 0 1 21 1P1d3f5b67c8f0ad2b 0 1 1 1P1fdd4aa57af222c0 0 4 0 1 2 1 37 1 38 1P201f7843cd32cfe5 0 2 0 1 5 1P2050ef65a32c0f31 0 4 0 1 17 1 35 1 36 1P2100279e1480b2d4 1 1 8 3 1 1 47 1 48 1 4 2 2 46 2 49 2 50 16P22e4a6bcc82aabc0 0 6 1 1 3 1 23 1 31 1 38 1 39 1P2366be271f916b5e 0 4 0 1 2 1 46 1 47 1P23e04c60101ef187 0 4 0 1 17 1 35 1 36 1P24b39c3252400630 1 1 8 3 0 1 47 1 48 1 6 2 2 31 2 39 2 46 2 49 2 50 16P24cc2049b5a8f0fd 1 1 8 3 0 1 37 1 40 1 4 2 2 38 2 39 2 41 16P2512f960e40b3f51 0 4 0 16 10 16 44 16 45 16P2637c811715764f5 0 4 1 1 2 1 46 1 47 1P286c3854c8dba84d 1 1 8 3 1 1 38 1 39 1 6 2 2 22 2 30 2 37 2 40 2 41 16P29ac2afaa64d1aec 0 2 0 1 1 1P2ab06fb50004bf51 0 2 0 1 6 1P2b28413ed97ea349 0 2 0 1 3 1P2b8a7bd168fa3e15 0 2 0 1 33 1P2c03b9a5597e55d1 1 1 8 3 1 1 38 1 39 1 6 2 2 22 2 30 2 37 2 40 2 41 16P2c60e6e310fe05fb 2 17 1 1 8 3 1 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 2 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2ce9cfe60544a7d3 1 1 8 3 0 1 46 1 49 1 4 2 2 47 2 48 2 50 16P2d622a315cdc0180 1 1 8 3 1 1 47 1 48 1 6 2 2 31 2 39 2 46 2 49 2 50 16P2f704e94958af2e0 0 2 0 1 5 1P30233a6d813c1718 1 1 16 2 0 1 35 1 3 2 1 36 1 37 16P31ceddca48007b23 0 2 0 1 3 1P326b66d43e1647f1 1 1 8 3 1 1 38 1 39 1 6 2 2 22 2 30 2 37 2 40 2 41 16P35d1c70788f9cf7e 0 2 0 1 3 1P36acf425be38c175 1 1 8 3 0 1 46 1 49 1 4 2 2 47 2 48 2 50 16P371ade55958ec2ac 1 1 8 3 1 1 47 1 48 1 6 2 2 31 2 39 2 46 2 49 2 50 16P37d782db71b894f0 0 4 1 1 2 1 46 1 47 1P37fbdab74bf82f78 1 1 8 3 1 1 37 1 40 1 4 2 2 38 2 39 2 41 16P3802876351f65106 1 1 8 3 1 1 46 1 49 1 4 2 2 47 2 48 2 50 16P389628f7bd719aca 1 1 8 3 0 1 37 1 40 1 4 2 2 38 2 39 2 41 16P38ac757dec5b6d8f 0 4 0 1 3 1 38 1 39 1P39a439ff56185e1b 1 1 8 3 1 1 46 1 49 1 4 2 2 47 2 48 2 50 16P39b0a4e018e36f08 0 4 0 1 2 1 37 1 38 1P39e404a2be691bf6 0 3 0 1 4 1 34 1P3c851a9bf7d3ab14 2 18 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P3cb4f606f24e4673 0 6 0 16 14 16 29 16 37 16 44 16 45 16P3df3de20808b06d1 1 1 8 3 1 1 38 1 39 1 6 2 2 22 2 30 2 37 2 40 2 41 16P3e78a0ea620bddc0 1 1 8 3 0 1 37 1 40 1 4 2 2 38 2 39 2 41 16P3e95015abf665ae7 0 6 0 16 5 16 20 16 28 16 35 16 36 16P3f550886b919f5fa 1 1 8 3 0 1 46 1 49 1 4 2 2 47 2 48 2 50 16N01047023bfa4e75cN017e851a53c81e2cN028cef082d7f532bN02e71c2b4af61be1N03127c5ba57de054N036c2d16f1f19fefN03ec4991efc276eeN04707d5f81069274N051eaf3cd8c330a6N059d41769eef7c52N062d8e7085c87b31N075360d6610ffbc3N081c61d1207ac631N098eecd4a319c068N0a7ec1152d930881N0a8b9a92a432aae7N0accb95deae13b79N0b3fce567b7f3674N0b7adec262e0bbb9N0bbb9b1b389f515dN0bedf4b7f57cebc9N0c282ab6aa5ca531N0d4bebb697522457N0d9e9806c058d635N10912416ed3e1713N110d0e197aeed6a9N12498db63d43ab3fN153acf5bec300df0N154564eb1a3374aaN15eeecac03ed7ee8N1788eccdf9f3d8a7N17b1c87c72c31a99N17d4de1131c3e594N1826341e53030cc2N189a1c84bf444ea7N1922c2668282303cN1929e8f70a659a66N194d407abc1710c7N19e43130777a4052N19eddab240498c45N1a26cad60d298ab0N1a8216a40937dc03N1a94bdee00309e4bN1ab995b0165e62f7N1b2604a2c78aca0bN1bc4fbfdae8603d8N1cd4ce7562c2d1a5N1d2c403a5def93fbN1db7a5c566385116N1e24ebdbddfca167N1e571cf968dac6c2N1e8619f2f2d11df1N1ea750ac3eb38d18N20f3f995eee94973N20f4d0f2314fc614N2100f86c0606117fN229d699d04f977b9N22a9ada357117e56N2462d3510c3e55e4N24a11c18eb2fd2ddN2687186ff057da98N29507df3a6e84098N2a010e5ec63da7dbN2b63cdc67db5b589N2bdd92cb1f0bfad2N2be9b3cf6b2542d0N2c0ef83b806ac903N2c49f36479b71c91N2c7b946db28d7f8fN2d9f97f6f3a2ce67N2db050c42fd559ecN2dbbb7ef1ae40b16N2ddfd51e3ec18a3dN2df432c841069febN2e969698dc484abaN2ef2e961e07544c5N2f557a5f58380e57N2f589f6d4baa6e59N2fa8d3c136200c6cN2fd6b688261f6317N30e07ec5003b5358N328a86f41f447ebfN32fbdaed1ee95581N33a5d907e9a2fa66N340d4d726c6b5a3aN3600a0de81172d3bN3745c180c7a7aa2fN374a4a04a1ab183eN3788fd1de6570038N38888624a3b11f99N3936fb2cbc155a2dN3992c93a8baeb5beN3bb9bba78dbc34a4N3bbc0f4652f635aaN3bcb0b7593773c9bN3c8fe93d654dffe1N3d27a2ad633b6d2bN3dbe6cc094419dc4N3ddf78e4ae0b58d1"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_parse_san_C () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.rev"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_parse_san_A.x509_parse_san_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (SB SAN BUF sp0 slen lo : Z) (bs : list byte).
  Notation CTX := (san_ctx usegs L HI U_CALLOC U_FREE sp tp h LB SB SAN BUF sp0 slen lo bs).
  Hypothesis HC : CTX.

  Notation X := [(SAN, SAN + 80)].
  Notation W := [(SAN, SAN + 80); (bv_unsigned sp - 80, bv_unsigned sp)].
  Notation POST := (x509_parse_san_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB SAN lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Let epi_walk' := epi_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let IBB := in_block_below' L HI sp tp h LB SB SAN BUF sp0 slen lo bs HC.
  Let heap_W' := heap_W L HI sp tp mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let presx_W' := presx_W L HI sp tp m h LB SB SAN BUF sp0 slen lo bs HC.
  (* [comment removed for export] *)
  Ltac call_memset :=
    let SPM := fresh "SPM" in
    pose proof U_memset_spec as SPM; unfold memset_stmt in SPM;
    lazymatch goal with
    | |- aevtM ?segs _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply aevtM_cut_evt;
        [ eassumption
        | eapply SPM; rewrite ?(unsigned_lit SAN) by dlia; rewrite ?(unsigned_lit 80) by (clear; lia); try eassumption
        | unfold memset_post; rewrite ?(unsigned_lit SAN) by dlia; rewrite ?(unsigned_lit 80) by (clear; lia);
          rewrite ?(unsigned_lit 0) by (clear; lia); post_call segs mx ]
    end;
    clear SPM;
    match goal with H : rw_cells _ _ SAN _ |- _ => change (Z.to_nat 80) with 80%nat in H; change (0 mod 256) with 0 in H end.


  (* [comment removed for export] *)
  Ltac ro_const A n RO :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
      let bs := eval vm_compute in (match image_bytes sg A n with Some bs => bs | None => [] end) in
      match goal with MI : mem_inv sg mx |- _ =>
        pose proof (ro_image_bytes_at sg mx A bs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO end
    end.

  (* [comment removed for export] *)
  Ltac san_t0 HSAN :=
    lazymatch type of HSAN with rw_cells ?sg ?mx ?A _ =>
      apply (rw_cells_zeros sg mx A 80 [C4 (Z_to_bv 64 0); CB 76 (repeat (Z_to_bv 8 0) 76)]) in HSAN;
        [| cbn; (flsplit; repeat split); reflexivity | reflexivity] end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HC => idtac end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L30467547904.2 L41474026096.3 L41476122939.2 L49538325459.98L56605192414.1 L61492275334.2 L65210688300.3 L65212784743.2 00000600700>00k01001601701>S1r2HrFS1t3Ht7S1L2HI2sp1h2SB3SAN2bs4rest2hc2HT4NZSB3NZS3SPRS3SANS1r2HrFS1t3Ht7". (* [comment removed for export] *)
  Lemma epi_gen : forall (r t dn : Z) (rest : list cell) (nodes : list Z) (pw lw : word)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) mm (moc : Model) (hc : HST usegs L HI),
    rw_cells usegs mm (bv_unsigned sp + -80) [C8 pw; C8 lw; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mm lo (bv_unsigned sp + -80) -> mem_inv usegs mm -> mo_frame mo moc ->
    heap_top usegs L HI hc = heap_top usegs L HI h ->
    HEAP usegs L HI hc (map (fun a : Z => (a, 64)) (rev nodes) ++ LB) mm moc ->
    heap_presx usegs L LB (bv_unsigned sp) X m mm ->
    -12288 < r <= 0 ->
    rw_cells usegs mm SAN (C4 (Z_to_bv 64 t) :: rest) -> Z.of_nat (cells_size rest) = 76 ->
    (t = 4 -> exists (p4 j48 : list byte) (mg : byte) (pad7 j8 : list byte), rest = CB 4 p4 :: name_blob j48 dn mg pad7 ++ [CB 8 j8]) ->
    (t = 4 -> name_chain usegs (fun _ : list cell => True) mm (map (fun a : Z => (a, 64)) (rev nodes) ++ LB) dn nodes) ->
    (t <> 4 -> nodes = []) -> (r <> 0 -> nodes = []) -> Stdlib.Lists.List.NoDup nodes ->
    (forall x : Z, In x nodes -> forall B k : Z, In (B, k) LB -> x + 64 <= B \/ B + k <= x) ->
    0 <= t <= 7 ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28c40) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros r t dn rest nodes pw lw x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 mm moc hc
    FR ST MI MF HT HH HPX Hr HSAN HSZ Hsh Hch Ht4 Hr0 HND HAP Ht7.
  open_sctx HC.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
  lxp_run (PLAN [0x1e5b8; 0x27d34; 0x28b70; 0x46940; 0x46e44] [] 216%N).
  lxp_ret_open.   (* [comment removed for export] *)
  apply aevtM_done.
  unfold x509_parse_san_post.
  flexi 15%nat.
  exists mm, moc, hc, r, t, dn, rest, nodes.
  split; [reflexivity|].
  (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption; try reflexivity; first [clear -Hr; lia | clear -Ht7; lia].
  all: lxp_ret_close.
  (* [comment removed for export] *)
  Unshelve. all: try lxp_default.   (* [comment removed for export] *)
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L28153927999.3 L57628698881.12L57628698881.9 L57628703851.1000000900_00o01PS2sp1a2HsS1L2sp3SAN2lo3HLS3SLO3ACL3DHI1a3Hd12HoS2sp3SAN1a2Hs2HoS1L2sp3SAN2lo3HLS3SLO3ACL1a2Ho2HY". (* [comment removed for export] *)
  Lemma presx_name : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san_C ()) "Pm5,P,(3.&40.)(4.(3.&8.))Pm6,P,(3.&40.)(4.(3.&8.))P,(19.$7.VL,VLB,(9.(:.&40.Vsp,)-50.)(;.(15.$0.$0.)(17.$0.$0.(9.(:.&40.Vsp,)-50.)(9.(9.(:.&40.Vsp,)-50.)+8.))(;.(15.$0.$0.)(17.$0.$0.(9.VSAN,+8.)(9.(9.VSAN,+8.)+40.))(=.(15.$0.$0.))))R2.R1.)(19.$7.VL,VLB,(:.&40.Vsp,)(;.(15.$0.$0.)(17.$0.$0.VSAN,(9.VSAN,+50.))(=.(15.$0.$0.)))R3.R2.)")
(* [comment removed for export] *).
  Proof.
    open_sctx HC. clear -ACL SLO HLS DHI IBB.
    intros m5 m6 HP a Ha Hc Ho. cbn [outside] in Ho. apply HP; [exact Ha| |].
    - destruct Hc as [Hs|[Hd|Hb]]; [left; clear -Hs; lia| right; left; exact Hd| right; right; exact Hb].
    - cbn [outside]. destruct Hc as [Hs|[[Hd1 Hd2]|Hb]]; [clear -Ho Hs SLO HLS; lia| clear -Ho Hd1 Hd2 DHI ACL SLO HLS; lia|].
      pose proof (IBB a Hb) as HY. clear -Ho HY ACL SLO HLS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L19027006488.166L19027007141.208L23515841079.109L25328010550.167L25328010550.204L26099205115.208L29316726604.210L31944022507.208L32847017047.1  L36423570177.5  L41737403597.209L43658457278.5  L52847871994.166L56220263264.166L56220263264.203L57628698881.4  L62246953235.1  00000>00L00Z00h01601R01`01n02302D02R02b03=03K03Y03f03kS2sp2SB3SAN2bsS2sp2SB3SAN2bsS2sp2SB3SAN2bsS2sp2SB3SAN2bsS2sp2SB3SAN2bsS2sp2SB3SAN2bs5lxv303H123H16S2sp2SB3SAN2bsS2sp2SB3SAN2bsS3SANS1L2sp2lo3HLS3SLOS2sp2SB3SAN2bsS1L2HI2sp1h4HTOPS2sp2SB3SAN2bs5lxv132H83H16S2sp2SB3SAN2bsS2sp2SB3SAN2bsS2sp3SAN1a2HoS3SAN". (* [comment removed for export] *)
  Lemma dir_walk : forall (w0 pw lw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -80) [C8 pw; C8 lw; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm SB [C8 w0; C8 (Z_to_bv 64 slen); C8 (Z_to_bv 64 sp0)] ->
    rw_cells usegs mm SAN [CB 80 (repeat (Z_to_bv 8 0) 80)] ->
    bytes_at usegs mm BUF bs ->
    stk usegs mm lo (bv_unsigned sp + -80) -> mem_inv usegs mm ->
    munch W m mm -> wmono usegs m mm -> HEAP usegs L HI h LB m mo ->
    aevtM usegs mo POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 SAN) (Z_to_bv 64 SB) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28b70) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros w0 pw lw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 mm FR HSB HSAN HBUF ST MI MU WM HH.
    open_sctx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    (* [comment removed for export] *)
    pose proof (heap_W' m mm HH MU WM) as HHm.
    pose proof (heapkit_introX L HI h LB mm mo [(lo, heap_top usegs L HI h); (SAN, SAN + 80)] HHm
       ltac:(constructor; [apply ok_stack; exact ACL | constructor; [apply (ok_cwrange L LB lo); [exact CWS | exact ACL] | constructor]])) as HK.
    pose proof (hcliX_cwrange L LB lo _ (bv_unsigned sp) SAN 80 CWS DSS) as T1.
    pose proof (cwo_stack L LB lo (heap_top usegs L HI h) (bv_unsigned sp + -80) 8 ltac:(clear -SLO HLS; lia) ltac:(clear -HTOP; lia)) as O1.
    pose proof (cwo_sub L LB lo (heap_top usegs L HI h) SAN 80 (SAN + 8) 64 CWS ltac:(clear; lia) ltac:(clear; lia)) as O2.
    pose proof (cro_crange L LB lo (heap_top usegs L HI h) BUF (Z.of_nat (length bs)) CRBUF) as O3.
    rewrite TP.
    lazymatch goal with |- aevtM _ _ ?Q _ =>
    assert (SU : Forall (summary_okMR usegs lx_no_layout (GS7 L lo (heap_top usegs L HI h)) [] [] (PROPS3 L LB lo (heap_top usegs L HI h)) LB
                          (hpP L HI (heap_top usegs L HI h) mo) (cwP L (heap_top usegs L HI h)) (LH2 L) (HRS1 L) (tgt_aevtM usegs Q) (fun _ => True))
                   [SUM_memset0P 80; SUM_gettagP; SUM_getnameP])
      by (constructor; [apply sum_plain_MR; [reflexivity| apply sum_memset0P_valid; cbn; lia]|];
          constructor; [apply sum_plain_MR; [reflexivity| apply sum_gettagP_valid]|];
          constructor; [eapply apply_summary_soundMR; apply (sum_getnameP_valid L HI HCALLOC HFREE HLS DIM1 DIM2 DHI)| constructor])
    end.
    lx_run_tac (PLANS [0x28c40; 0x46940] [] 216%N [SUM_memset0P 80; SUM_gettagP; SUM_getnameP]); lx_tree.
    (* [comment removed for export] *)
    all: (let flt1 := fresh "FLt" in let flt2 := fresh "FLt" in flat constr:(LXHK) 2%nat; flclear LXHK; intros flt1 _; flat constr:(flt1) 2%nat; flclear flt1; intros flt2 _; flat constr:(flt2) 4%nat; flclear flt2; intros hc HHc HTc MFc); rewrite <- TP.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hp : rw_cells _ mx (bv_unsigned sp + -80) [_], Hl : rw_cells _ mx (bv_unsigned sp + -72) [_], Hf : rw_cells _ mx (bv_unsigned sp + -64) _ |- _ =>
           chunk_join Hp Hl LXFR1; chunk_join LXFR1 Hf LXFR end end.
    (* [comment removed for export] *)
    all: lazymatch goal with Hm : munch _ m ?mx, Hw : wmono _ m ?mx |- _ => pose proof (presx_W' _ _ (heap_presx_refl usegs L LB (bv_unsigned sp) X m) Hm Hw) as LXPX1 end.
    2-3: lazymatch goal with Hl : lawPX L LB _ _ ?mc ?mp, Hm : munch [] ?mp' ?mx, Hw : wmono _ ?mp'' ?mx' |- _ =>
           assert (LXPX : heap_presx usegs L LB (bv_unsigned sp) X m mx);
           [ eapply heap_presx_trans; [exact LXPX1|]; eapply heap_presx_trans;
             [ apply presx_name; unfold lawPX in Hl; intros a Ha Hc Ho; apply (Hl a Ha Hc); revert Ho; cbn [outside]; clear; intros Ho; lia
             | eapply (heap_presx_of_munch usegs L); [exact Hm| exact Hw| intros a _ _ _; exact I] ]
           | clear LXPX1 ] end.
    (* [comment removed for export] *)
    2-3: lazymatch goal with HR : lx_hres _ _ _ (RnameP L) _ ?lb _ _ ?mx |- _ =>
           (let flt3 := fresh "FLt" in flat constr:(HR) 2%nat; flclear HR; intros flt3 _; flat constr:(flt3) 7%nat; flclear flt3; intros nodes LXE HND HAP HBR HCH Hr0); subst lb; cbn [nth] in HCH, Hr0 end.
    2-3: lazymatch goal with Hc : rw_cells _ ?mx (SAN + 8) [_; _; _; _; _; _; _; _], Hs : rw_cells _ ?mx' SAN [_; _], Ht : rw_cells _ ?mx'' (SAN + 72) [_] |- _ =>
           apply words_name_blob in Hc; (flat constr:(Hc) 4%nat; flclear Hc; intros j48 mg pad7 Hc); chunk_join Hs Hc LXS1; chunk_join LXS1 Ht LXSAN end.
    - (* [comment removed for export] *)
      lazymatch goal with Hs : rw_cells _ ?mx SAN ?cs |- _ =>
        apply (rw_cells_reshape usegs mx SAN cs (C4 (Z_to_bv 64 4) :: CB 4 (repeat (Z_to_bv 8 0) 4) :: name_blob (repeat (Z_to_bv 8 0) 48) 0 (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 7) ++ [CB 8 (repeat (Z_to_bv 8 0) 8)]))
          in Hs; [| cbn; (flsplit; repeat split); reflexivity | vm_compute; reflexivity] end.
      eapply epi_gen with (nodes := []) (dn := 0) (t := 4) (hc := hc); try eassumption.
      all: first [ cbn [map rev app]; eassumption | solve [cbn; reflexivity] | solve [intros _; flexi 5%nat; reflexivity]
                 | solve [intros _; apply chain_nil] | solve [intros _; reflexivity] | solve [constructor] | solve [intros ? []] | lia ].
    - (* [comment removed for export] *)
      lazymatch type of HCH with name_chain _ _ _ _ ?dnv _ => eapply epi_gen with (t := 4) (dn := dnv) (nodes := nodes) (hc := hc); try eassumption end.
      all: first [ solve [cbn; reflexivity] | solve [intros _; flexi 5%nat; reflexivity] | solve [intros _; exact HCH]
                 | solve [intros ?N; exfalso; exact (N eq_refl)] | lia ].
    - (* [comment removed for export] *)
      lazymatch type of HCH with name_chain _ _ _ _ ?dnv _ => eapply epi_gen with (t := 4) (dn := dnv) (nodes := nodes) (hc := hc); try eassumption end.
      all: first [ solve [cbn; reflexivity] | solve [intros _; flexi 5%nat; reflexivity] | solve [intros _; exact HCH]
                 | solve [intros ?N; exfalso; exact (N eq_refl)] | lia ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

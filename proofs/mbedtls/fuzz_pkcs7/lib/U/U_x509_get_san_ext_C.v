(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_len U_asn1_sequence_free U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_parse_san_A U_x509_parse_san U_x509_get_san_ext_A U_x509_get_san_ext_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P024f4a071cbde3cd 0 3 0 1 33 1 34 1P03b5b0d9ebb57840 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P05836ca6d42d9468 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P05de22bc2bb6eea9 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P0afefcd8372d58d7 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P0f515145b3c53d41 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P119a40d79758258a 2 24 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P147f90282cde6cd2 0 5 0 1 22 1 30 1 45 1 46 1P19ed8253525d7e1a 2 67 1 1 8 3 1 1 67 1 68 1 6 0 1 44 1 51 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P1d0e45e6250e4c06 2 58 1 1 8 3 1 1 63 1 64 1 6 0 1 40 1 47 1 62 1 65 1 66 8 1 1 8 3 2 1 62 1 65 1 4 0 1 63 1 64 1 66 8P1ed95d32d18daa58 0 6 0 1 22 1 30 1 35 1 47 1 48 1P1f09ccc390009d30 2 67 1 1 8 3 1 1 67 1 68 1 6 0 1 44 1 51 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P1f6e0ee449a6eed5 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P21ced7c239a39a32 0 2 0 1 54 1P230cea51e795a5b7 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P243bcee82865e2b1 2 24 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P24c30d9521b60c61 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P26ef562b8967f815 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P289b407144339757 1 2 16 2 0 1 64 1 16 2 29 1 65 1 2 66 1 67 1P2ae81e0ff4d982cf 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P2c9ed1342eb79ad7 0 4 0 16 13 16 64 16 65 16P2d66bff44cfd6e29 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P2d84a8cc8eb18533 2 24 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P2fd5e143db63a338 2 49 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P3b1c4ab5997dce96 2 67 1 1 8 3 1 1 67 1 68 1 6 0 1 44 1 51 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P3ba1b0a19be34254 2 58 1 1 8 3 1 1 63 1 64 1 6 0 1 40 1 47 1 62 1 65 1 66 8 1 1 8 3 2 1 62 1 65 1 4 0 1 63 1 64 1 66 8P3cfe5322d8e69b43 2 58 1 1 8 3 1 1 63 1 64 1 6 0 1 40 1 47 1 62 1 65 1 66 8 1 1 8 3 2 1 62 1 65 1 4 0 1 63 1 64 1 66 8P3d008a54929b88d4 0 4 0 1 33 1 34 1 45 1P3d68a568d9b6fbc6 2 67 1 1 8 3 1 1 67 1 68 1 6 0 1 44 1 51 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P3e20bb109f150fc9 1 1 16 2 29 1 65 1 3 0 1 64 1 66 16P3e64e68c5727790c 2 24 1 1 8 3 1 1 56 1 57 1 6 0 1 31 1 38 1 55 1 58 1 59 8 1 1 8 3 2 1 55 1 58 1 4 0 1 56 1 57 1 59 8P3feb0e7df5269c08 2 58 1 1 8 3 1 1 63 1 64 1 6 0 1 40 1 47 1 62 1 65 1 66 8 1 1 8 3 2 1 62 1 65 1 4 0 1 63 1 64 1 66 8N0022d580a05297ceN00538447713ddd20N009756eef7ad9389N00c179790a4e6751N01e7bc5196763a9bN038115a34d9d6063N04f948a235e83fb8N05a1d4f61eb21c62N080cd700bb883f94N093d9c6d7b929f8cN0aba12b74d34df5bN0b22ed69012143b6N0bf69efaed6fbadaN0c5cb1a66c85435bN0c988772f13f4d91N0efcb3759c02e1eaN0ff9321aee32d06aN10a1b9be935ffb5eN12177785a423de98N142f5b84cb15302bN14597dec93f0d44fN164dcbdbad7fdac9N179b089baa0f9770N18941780743e7792N189451dfbb06b903N18bd0b09b50e872bN19ca4b001474fdc3N19e04e36142daeb8N1b2def8f0be7af68N1b5782c845ba0faeN1bbb5da4c145d9f0N1c6e6943e90363faN1d0d6a0e9a47ce9bN1ea2c54ecab2ed72N1fcfc51ced6dd0d3N203a5532673bc32dN206d5a733ea7ac71N20980699167e4ac5N2130f27cc02f119cN21d589d47ed4e388N2248bbf460a92c82N23362e71d0c0c265N236b79dfab3ba21aN2430defacbb90d74N24337b0619ffb776N24479a3339484dbbN2536e6352bf818b5N26033266b0abf599N2641651953ee65b9N26911ef608e09e67N26bebdf6c0e1a7b0N26de8585907c66f0N27985ced1d7ba771N291f6c7db2fcd8c9N2b3ef7494ae043b7N2bef79e951710bd2N2e0f4ceea7a26a5cN2ec07b4fd173fee5N2f2d7665f9e19cbdN2ffce8a1bd8b29e5N3037fb2ef65e1263N305667408f1917f4N30fabb7c5f786907N31c984b2dd1991f1N31d66b2f19b27122N32500d779bdbc917N33edab723e750829N3520e36a62e994a2N35f21b6547c9693eN35f7b5eee2fb12ceN36180a1bc9f45718N3804274a79f11510N3862473aed3551aeN38698a58f015cfffN3872b13d104692b5N3c7bf08119ec0bcdN3de36f03f7cf8b3dN3ebd68977c1b7acbN3f0c891f07d521b0N3fd4e1c6ec40a741N3fddadc514890162"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_san_ext_C () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.ninv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.x509_get_san_ext_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Walk.BodyOb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.curF"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.nLBof"; "Stdlib.Lists.List.removelast"; "Stdlib.Lists.List.last"; "Stdlib.Lists.List.In"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (bs : list byte).
  Notation CTX := (ext_ctx usegs L HI U_CALLOC U_FREE sp tp h LB PP CUR P END BUF lo bs).
  Hypothesis HC : CTX.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (x509_get_san_ext_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -224)).
  Notation INV := (ninv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo h LB PP CUR END BUF lo bs).
  Notation K4W := (Z_to_bv 64 (-9570)) (only parsing).
  Notation K7W := (Z_to_bv 64 (-9472)) (only parsing).
  Notation K8W := (Z_to_bv 64 (-8320)) (only parsing).
  Notation K9W := (Z_to_bv 64 (-9578)) (only parsing).
  Let sync_W' := sync_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let presx_W' := presx_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let heap_W' := heap_W L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let snoc_facts' := snoc_facts L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let others_apart' := others_apart L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_wrange' := cur_wrange L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_pres' := headrep_pres L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_presx' := headrep_presx L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let presx_call' := presx_call L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_cases' := cur_cases L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let in_block_below' := in_block_below L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let close_nodes' := close_nodes sp LB PP CUR END BUF lo bs.
  Let headrep_snoc' := headrep_snoc sp PP CUR END BUF lo bs.
  Let presx_munch' := presx_munch L sp LB PP CUR.

  Ltac open_ninv INV :=
    pose proof INV as INVc;
    (flat constr:(INVc) 19%nat; flclear INVc; intros HH HT HND HFR HCF HHD HLS' F0 FB SZB FS SZS FT FRH ST MI HBUF HPX MF);
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; pose proof (conj HH I) as HHbox;
    pose proof HCF as HCFc; (flat constr:(HCFc) 7%nat; flclear HCFc; intros CAL CPOS C32 CPP CBF CSTK _);
    try unfold frame_hi in FRH.

  (* [comment removed for export] *)
  Ltac start_W cur :=
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (W sp PP cur) mx) as MU; unfold W in MU; pose proof (wmono_refl usegs mx) as WM end.

  (* [comment removed for export] *)
  Ltac wsync :=
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with
      | HHbox : HEAP _ _ _ ?hc ?LBx ?mm ?moc /\ True, HT : heap_top _ _ _ ?hc = _, HCF : curF _ _ _ _ _ _ ?nodes ?cur,
        HND : List.NoDup ?nodes, HFR : nfresh _ _ ?nodes,
        MU : munch _ ?mm mx, WM : wmono _ ?mm mx, HHD : headrep CUR END BUF ?mm ?nodes,
        HLS' : seq_lseg _ ?mm _ BUF END (removelast ?nodes) _, HPX : heap_presx _ _ LB _ _ m ?mm |- _ =>
          let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
          let HS := fresh "HS" in
          assert (HS : forall b, In b (nLBof LB nodes) -> In b LBx)
            by first [ exact (fun b Hb => Hb) | exact (fun b Hb => or_intror Hb) | solve_sub ];
          repeat match goal with H : HEAP _ _ _ _ _ _ _ |- _ => clear H end;
          repeat match goal with H : MOK _ |- _ => clear H end;
          (flat constr:((sync_W' _ _ _ _ _ _ _ _ _ (proj1 HHbox) HT HS HND HFR HCF HHD HLS' HPX MU WM)) 4%nat; intros A B C D); clear HS;
          clear HHbox HHD HLS' HPX MU WM;
          match goal with HHn : HEAP _ _ _ _ _ mx _ |- _ => pose proof (conj HHn I) as HHbox; pose proof (heap_mok _ _ HI _ _ _ _ HHn) as MK end;
          rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
          pose proof (munch_refl (W sp PP cur) mx) as MU; unfold W in MU; pose proof (wmono_refl usegs mx) as WM
      end
    end.

  (* [comment removed for export] *)
  Ltac rebuild_ninv INVn :=
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with
    | HH : HEAP _ _ _ ?hc (nLBof LB ?nodes) mx mox, HCF : curF _ _ _ _ _ _ ?nodes ?cur,
      F0 : rw_cells _ mx (bv_unsigned sp + -224) [CB 8 ?j0], FB : rw_cells _ mx (bv_unsigned sp + -216) ?fb,
      FS : rw_cells _ mx (bv_unsigned sp + -192) ?fs, FT : rw_cells _ mx (bv_unsigned sp + -112) [C8 ?tl] |- _ =>
        assert (INVn : INV mx mox hc nodes cur j0 fb fs tl);
        [ unfold ninv; repeat match goal with |- _ /\ _ => split end; try assumption;
          try (simpl_sizes; reflexivity);
          try (etransitivity; eassumption); try (eapply mo_frame_trans; eassumption) | ]
    end end.

  (* [comment removed for export] *)
  Definition BodyOb (p : Z) : Prop :=
    forall (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (fb fs : list cell) (tl : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI),
    INV mm moc hc nodes cur j0 fb fs tl -> rw_cells usegs mm cur (seq_cells ct cpad cl cp 0) ->
    (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p)] -> P <= p -> p < END ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (-9570)) (Z_to_bv 64 PP) (Z_to_bv 64 (-1)) (Z_to_bv 64 cur) (Z_to_bv 64 128) (Z_to_bv 64 4)
             (Z_to_bv 64 (-9472)) (Z_to_bv 64 (-8320)) (Z_to_bv 64 (-9578)) (Z_to_bv 64 p) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2880c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Let exit_walk' := exit_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs HC.
  Let epi_inv' := epi_inv L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs HC.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.52L18926747689.52L18926759668.5200000:00;00@S1a1b1k2HkSS1a1b". (* [comment removed for export] *)
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
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
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := spine_firstn k cs in
      let l2 := spine_skipn k cs in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
    end.

  (* [comment removed for export] *)
  Ltac cells_upto cs n :=
    lazymatch n with
    | 0%nat => constr:(0%nat)
    | _ => lazymatch cs with ?c :: ?cs' => let k := eval cbn in (n - csize c)%nat in let r := cells_upto cs' k in constr:(S r) end
    end.
  Ltac cutsz mx A n :=
    try (lazymatch goal with H : rw_cells _ mx A ?cs |- _ =>
      let tot := eval cbn in (cells_size cs) in
      lazymatch eval compute in (Nat.ltb n tot) with
      | true => let k := cells_upto cs n in let H2 := fresh "FX" in splitat H k H2
      | false => idtac end end).
  (* [comment removed for export] *)
  Ltac cut_locals mx :=
    cutsz mx (bv_unsigned sp + -224) 8%nat; cutsz mx (bv_unsigned sp + -216) 24%nat;
    cutsz mx (bv_unsigned sp + -192) 80%nat; cutsz mx (bv_unsigned sp + -112) 8%nat.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L12574255052.159L12574255052.168L26353550635.148L30132237391.148L31952411677.148L41660124335.148L57626602889.5  L8840411291.148 00000102P03@04F05A06M06_082FS1L2sp2PP3CUR1P3END3BUF2lo2bs2p02p12Lw2tb2pd3cur2fs3Hp04Hp013Hp12HL3SZB3SZS3CAL4CPOS3CPP3CBF4CSTK3HLS2B12B32D12D22D33PPB4CURB3AL13SLO3SPA3DS13DS23DS33SPR2LR2H7S2sp2PP3CUR3END2bs2p12Lw2tb2pd3cur2fs3SZB3SZS2H7S2sp2PP3CUR2bs2p02p12Lw2tb2pd3cur2fs4Hp013SZB3SZS4CPOS3PPB4CURB3SPR2LRS2sp2PP3CUR3END3BUF2bs2p12Lw2tb2pd3cur2fs3Hp12HL3SZB3SZS2LRS2sp2PP3CUR1P2bs2p02p12Lw2tb2pd3cur2fs3Hp04Hp013SZB3SZS4CPOS3PPB4CURB3SPR2LRS2sp2PP3cur2xw3HxwS2sp2PP3CUR1P3END2bs2p02p12Lw2tb2pd3cur2fs3Hp04Hp012HL3SZB3SZS4CPOS3PPB4CURB3SPR2LR". (* [comment removed for export] *)
  Lemma assign_walk : forall (p0 p1 : Z) (Lw tb pd : word) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (fs : list cell) (tl : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI),
    (forall p' : Z, p0 < p' -> BodyOb p') ->
    INV mm moc hc nodes cur j0 [C4 tb; C4 pd; C8 Lw; C8 (Z_to_bv 64 p1)] fs tl ->
    rw_cells usegs mm cur (seq_cells ct cpad cl cp 0) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p1)] -> P <= p0 -> p0 < p1 -> BUF <= p1 -> bv_unsigned Lw <= END - p1 ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (-9570)) (Z_to_bv 64 PP) (Z_to_bv 64 (-1)) (Z_to_bv 64 cur) (Z_to_bv 64 128) (Z_to_bv 64 4)
             (Z_to_bv 64 (-9472)) (Z_to_bv 64 (-8320)) (Z_to_bv 64 (-9578)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x288bc) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros p0 p1 Lw tb pd nodes cur ct cpad cl cp j0 fs tl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 mm moc hc
      KLOOP INV HCUR HPP Hp0 Hp01 Hp1 HL.
    open_ninv INV. clear INV. open_ectx HC. unfold seq_cells in HCUR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    clear HHbox.
    (* [comment removed for export] *)
    lazymatch type of FB with rw_cells ?sg ?mx ?A (C4 ?v :: C4 ?w :: ?rest) =>
      change (rw_cells sg mx A (C4 v :: C4 w :: rest)) with (rw_cells sg mx A ([] ++ C4 v :: C4 w :: rest)) in FB;
      apply (rw_cells_join_C4C4 sg mx A [] v w rest) in FB; cbn [app] in FB end.
    lazymatch type of HCUR with rw_cells ?sg ?mx ?A (C4 ?v :: C4 ?w :: ?rest) =>
      change (rw_cells sg mx A (C4 v :: C4 w :: rest)) with (rw_cells sg mx A ([] ++ C4 v :: C4 w :: rest)) in HCUR;
      apply (rw_cells_join_C4C4 sg mx A [] v w rest) in HCUR; cbn [app] in HCUR end.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS [0x2890c; 0x2880c] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         lazymatch goal with Hm1 : munch ?W1 ?mA mx, Hw1 : wmono _ ?mA' mx, HCFx : curF _ _ _ _ _ _ ?nodesx ?curx |- _ =>
           let MUW := fresh "MUW" in
           assert (MUW : munch (W sp PP curx) mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
           (* [comment removed for export] *)
           apply (rw_cells_transport usegs W1 mA mx) in FS; [| exact Hm1| exact Hw1| rewrite SZS; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia];
           let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
           destruct (sync_W' _ _ _ _ _ _ _ _ _ HH HT ltac:(intros bb Hbb; exact Hbb) HND HFR HCF HHD HLS' HPX MUW Hw1) as (A & B & C & D);
           clear HH HHD HLS' HPX MUW Hm1 Hw1 MK; rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
           pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK;
           try clear ST MI HBUF HCUR HPP F0 FB FT FRH;
           cut_locals mx;
           (* [comment removed for export] *)
           lazymatch goal with XC : rw_cells _ mx curx _ |- _ => split_c8 XC 0%nat; rewrite <- (Z_to_bv_bv_unsigned Lw) in XC end;
           rebuild_ninv INV2;
           lazymatch goal with XC : rw_cells _ mx curx _, XP : rw_cells _ mx PP _ |- _ =>
             lazymatch pc with
             | 166156 => eapply exit_walk'; [exact INV2| exact XC| right; flia| exact XP| flia]
             | _ => eapply KLOOP; [flia| exact INV2| exact XC| right; flia| exact XP| flia| flia]
             end end
         end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L50079274485.2600000QS3END3BUF2cl2cp5nodes3HB13HB23HB3". (* [comment removed for export] *)
  Lemma lseg_fin : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_C ()) "Pnodes,(0.$1.)Pcur,$1.Pmm,P,(2.&40.)(4.(2.&8.))Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$1.Pcp,$1.Pfin,$1.PLBx,(0.$1?.)P,(20.Vsp,VPP,VCUR,VBUF,Vlo,Vbs,R9.R8.)P,(21.$7.R8.(22.VLB,R:.)VBUF,VEND,(23.$1.R:.)(24.$1.R:.=))P,(9.$7.R9.R:.(:.R8.R7.R6.R5.R4.))P,(?.VBUF,R6.)P,(?.=R8.)P,(?.(10.R8.R9.)VEND,)P,Pb,$1?.P,(25.$1?.R1.(22.VLB,R10.))(25.$1?.R2.R9.)(21.$7.R>.R8.VBUF,VEND,R10.R9.)")
(* [comment removed for export] *).
  Proof.
    clear. intros nodes cur mm ct cpad cl cp fin LBx HCF HL HR HB1 HB2 HB3 HS.
    destruct nodes as [|n0 rest0]; [exact I|]. assert (Hne : n0 :: rest0 <> []) by discriminate. revert Hne HCF HL HS. generalize (n0 :: rest0). clear n0 rest0. intros nodes Hne HCF HL HS.
    destruct HCF as (AL & POS & _ & _ & _ & _ & [[E _]|(_ & -> & A16 & _)]); [exfalso; exact (Hne E)|].
    eapply seq_lseg_mem; [| intros x Hx; apply HS; apply nLBof_in; exact Hx| intros x cs _ HRx _; exact HRx].
    rewrite <- (removelast_last_app nodes 0) at 1 by exact Hne. apply seq_lseg_app. split; [exact HL|].
    cbn [seq_lseg hd]. split; [apply nLBof_in|].
    { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
    split; [exact A16|]. split; [exact POS|]. split; [| exact I]. exists ct, cpad, cl, cp. split; [exact HR| lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@D13331496663.178D13518748971.160D13680170334.178D14443090765.178D19699157982.178D35249408222.178D37835037753.178D43623715735.178D43634070499.160D44013068667.160D59328247518.178D6749623403.160 D7109767216.160 D8683277918.178 L11803471112.183L11803471112.192L11803471112.195L11803471112.208L1577139281.1   L22704459656.5  L24124040997.172L38397475527.172L49788159649.0  L59308580059.157L64009836305.14 L64481468488.1  R1734685728.178 R22196912988.178R22600905526.17800000100h01Q01R02;02d02e04505E05n06W07@08208[08\0:V0:W0=K0=O0=a0?40?]0?^0@L0A80A<0Am0B]0CQFS1L2HI2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs2hc3SZB3SZS5HTOPcS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSFS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSFS1L2sp2PP3CUR2lo2bs2p12Lw2tb2pd3cur2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO3ACL3ACP3SPRS1L2sp2PP3CUR2lo2bs2p12Lw2tb2pd3cur2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO3ACL3ACP3SPRS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSS1L2sp2PP3CUR2lo2bs2p12Lw2tb2pd3cur2fs3SZB3SZS3SLOS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSFS1L2sp2PP3CUR3BUF2lo2bs2p12Lw2tb2pd3cur2fs3SZB3SZS3CAL4CPOS3CPP3CBF4CSTK3HLS2D12D22D33PPB4CURB3SLO3SPA3DS13DS23DS33SPR3LBSFS1L2sp2PP3CUR1P3END3BUF2lo2bs2p02p12Lw2tb2pd3cur2fs3Hp04Hp012HL3SZB3SZS3CAL4CPOS3CPP3CBF4CSTK3HLS2B12B32D12D22D33PPB4CURB3SLO3ACL3SPA3DS13DS23DS33SPR2LR3LBS1N5APcur3APP3APB3HN03HNCS2spS2sp2PP3cur2xw3HxwS2sp2PP3CUR1P3END2bs2p02p12Lw2tb2pd3cur2fs3Hp04Hp012HL3SZB3SZS4CPOS3PPB4CURB3SPR2LRS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZSSS2sp2PP3CUR2bs2p12Lw2tb2pd3cur2fs3SZB3SZS4LXKFS1P3END3BUF2bs2p02p12Lw3Hp04Hp012HL2B12B32LRS2spS2sp2PP3CUR2lo2bs2p12Lw2tb2pd3cur2fs3SZB3SZS4CSTKS2sp2PP3CUR2lo2bs2p12Lw2tb2pd3cur2fs3SZB3SZS3DS1S2sp2PP3CUR3BUF2lo2bs2p12Lw2tb2pd3cur2fs3SZB3SZS3DS3". (* [comment removed for export] *)
  Lemma alloc_walk : forall (p0 p1 : Z) (Lw tb pd : word) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (fs : list cell) (tl : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI),
    (forall p' : Z, p0 < p' -> BodyOb p') ->
    INV mm moc hc nodes cur j0 [C4 tb; C4 pd; C8 Lw; C8 (Z_to_bv 64 p1)] fs tl ->
    rw_cells usegs mm cur (seq_cells ct cpad cl cp 0) ->
    (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p1)] -> P <= p0 -> p0 < p1 -> BUF <= p1 -> bv_unsigned Lw <= END - p1 ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (-9570)) (Z_to_bv 64 PP) (Z_to_bv 64 (-1)) (Z_to_bv 64 cur) (Z_to_bv 64 128) (Z_to_bv 64 4)
             (Z_to_bv 64 (-9472)) (Z_to_bv 64 (-8320)) (Z_to_bv 64 (-9578)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28888) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros p0 p1 Lw tb pd nodes cur ct cpad cl cp j0 fs tl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 mm moc hc
      KLOOP INV HCUR HCB HPP Hp0 Hp01 Hp1 HL.
    open_ninv INV. open_ectx HC. unfold seq_cells in HCUR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    assert (LBS : 0 < Z.of_nat (length bs)) by (clear -B1 B3 Hp0 Hp01 Hp1 HL LR; lia).
    clear HHbox.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS [0x288bc; 0x3f960] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    1: eapply assign_walk; [exact KLOOP| exact INV| exact HCUR| exact HPP| exact Hp0| exact Hp01| exact Hp1| exact HL].
    clear INV.
    assert (HCBr : BUF <= cp /\ 0 <= cl /\ cp + cl <= END) by (destruct HCB as [(E & _)|HCB']; [exfalso; subst cp; flia| exact HCB']).
    clear HCB.
    repeat match goal with H : munch [] ?a ?a |- _ => clear H | H : wmono _ ?a ?a |- _ => clear H end.
    (* [comment removed for export] *)
    repeat match goal with H : rw_cells _ mm ?A ?cs, H' : rw_cells _ mm ?A ?cs |- _ => clear H' end.
    repeat match goal with H : bytes_at _ mm BUF bs, H' : bytes_at _ mm BUF bs |- _ => clear H' end.
    repeat match goal with H : stk _ mm lo ?x, H' : stk _ mm lo ?x |- _ => clear H' end.
    repeat match goal with H : mem_inv _ mm, H' : mem_inv _ mm |- _ => clear H' end.
    pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
    pose proof CWc0 as CWc. rewrite <- HT in CWc. pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
    replace (Z_to_bv 64 260448) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 32) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -224)) by dlia; try eassumption; try reflexivity; try flia2 | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -224)) in PO by dlia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ _ m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame moc mo2 |- _ => rename H into MF2 end.
    pose proof (headrep_pres' nodes _ _ _ HPc (nLBof_sub LB nodes) HHD) as HHD2.
    pose proof (lseg_pres _ _ _ _ _ _ _ _ _ HPc HLS') as HLS2.
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) X m m2).
    { eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_pres_sub; [exact HPc| apply nLBof_sub| clear; lia| clear; lia]. }
    clear ST MI MK HH HHD HLS' HPX. heap_transport HPc. clear HPc.
    rename HHD2 into HHD. rename HLS2 into HLS'. rename HPX2 into HPX.
    destruct PO as (h2 & HT2 & [[-> HH2] | (N & -> & HBN & HH2 & HNEW)]); rewrite HT in HT2; clear HT CWc HTOPc; rename HT2 into HT;
      pose proof CWc0 as CWc; rewrite <- HT in CWc; pose proof HTOP as HTOPc; rewrite <- HT in HTOPc.
    - (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. rename HH2 into HH.
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK).
      lx_run_tac (PLANS [0x28938; 0x288bc] [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP.
      all: repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
             let z := constr:(Zpos p) in
             lazymatch eval compute in (Z.leb (2^63) z) with
             | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
             end end.
      all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         lazymatch goal with Hm1 : munch ?W1 ?mA mx, Hw1 : wmono _ ?mA' mx, HCFx : curF _ _ _ _ _ _ ?nodesx ?curx |- _ =>
           let MUW := fresh "MUW" in
           assert (MUW : munch (W sp PP curx) mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
           apply (rw_cells_transport usegs W1 mA mx) in FS; [| exact Hm1| exact Hw1| rewrite SZS; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia];
           let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
           destruct (sync_W' _ _ _ _ _ _ _ _ _ HH HT ltac:(intros bb Hbb; exact Hbb) HND HFR HCF HHD HLS' HPX MUW Hw1) as (A & B & C & D);
           clear HH HHD HLS' HPX MUW Hm1 Hw1 MK; rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
           pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK;
           try clear ST2 MI2 HBUF HCUR HPP F0 FB FT FRH;
           cut_locals mx;
           rebuild_ninv INV2;
           lazymatch goal with XC : rw_cells _ mx curx _, XP : rw_cells _ mx PP _ |- _ =>
             eapply epi_inv'; [exact INV2| exact XC| right; exact HCBr| exact XP| flia| flia] end
         end end.
    - (* [comment removed for export] *)
      change (1 * 32) with 32 in HBN, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
      flat constr:((snoc_facts' nodes cur N h2 m2 mo2 HH2 HND HFR HCF HBN LBS)) 6%nat. intros HND' HFR' HCF' APcur APP APB.
      pose proof HBN as HBNc. flat constr:(HBNc) 5%nat. flclear HBNc. intros HN0 HN16 _ HNC HNI.
      apply (rw_cells_zeros usegs m2 N 32 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in HNEW;
        [| cbn; repeat split; reflexivity | reflexivity].
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. rename HH2 into HH.
      pose proof (cur_wrange' nodes cur ((N, 32) :: nLBof LB nodes) HFR HCF ltac:(intros b Hb; right; exact Hb)) as CW2. rewrite <- HT in CW2.
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK).
      lx_run_tac (PLANS [0x28938; 0x288bc] [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP.
      all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx | |- _ => idtac end.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) in * end.
      lazymatch goal with Hm1 : munch ?W1 m2 m3, Hw1 : wmono _ m2 m3 |- _ =>
        assert (MUW : munch (W sp PP cur) m2 m3) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
        apply (rw_cells_transport usegs W1 m2 m3) in FS; [| exact Hm1| exact Hw1| rewrite SZS; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia];
        destruct (sync_W' _ _ _ _ _ _ _ _ _ HH HT ltac:(intros bb Hbb; right; exact Hbb) HND HFR HCF HHD HLS' HPX MUW Hw1) as (HH3 & HHD3 & HLS3 & HPX3);
        clear HH HHD HLS' HPX MUW Hm1 Hw1 MK
      end.
      lazymatch goal with HC : rw_cells _ m3 cur _ |- _ => rename HC into HCUR3 end.
      lazymatch type of HCUR3 with rw_cells _ _ _ [_; _; _; _; C8 ?nv] => change nv with (Z_to_bv 64 N : word) in HCUR3 || idtac | _ => idtac end.
      change (rw_cells usegs m3 cur (seq_cells ct cpad cl cp N)) in HCUR3.
      flat constr:(HCBr) 3%nat. flclear HCBr. intros HB1' HB2' HB3'.
      pose proof (headrep_snoc' nodes cur m3 _ _ _ _ N HCF HHD3 HCUR3 HB1' HB2' HB3') as HHD4.
      pose proof (lseg_fin nodes cur m3 _ _ _ _ N ((N, 32) :: nLBof LB nodes) HCF HLS3 HCUR3 HB1' HB2' HB3' ltac:(intros b Hb; right; exact Hb)) as HLS4.
      rewrite <- nLBof_snoc in HH3, HLS4.
      clear HHD3 HLS3 HCF HND HFR CAL CPOS C32 CPP CBF CSTK HCUR3.
      cut_locals m3.
      lazymatch goal with X0 : rw_cells _ m3 (bv_unsigned sp + -224) [CB 8 _], XB : rw_cells _ m3 (bv_unsigned sp + -216) ?fb, XT : rw_cells _ m3 (bv_unsigned sp + -112) [C8 _],
                          XR : rw_cells _ m3 (bv_unsigned sp + -104) _, XN : rw_cells _ m3 N _, XP : rw_cells _ m3 PP _, STx : stk _ m3 lo _, MIx : mem_inv _ m3, HB : bytes_at _ m3 BUF bs |- _ =>
        assert (INV3 : INV m3 mo2 h2 (nodes ++ [N]) N j0 fb fs tl);
        [ unfold ninv; rewrite removelast_last, last_last;
          repeat match goal with |- _ /\ _ => split end; try assumption; first [reflexivity | eapply mo_frame_trans; eassumption]
        | change (rw_cells usegs m3 N (seq_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0)) in XN;
          eapply assign_walk; [exact KLOOP| exact INV3| exact XN| exact XP| exact Hp0| exact Hp01| exact Hp1| exact HL] ]
      end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

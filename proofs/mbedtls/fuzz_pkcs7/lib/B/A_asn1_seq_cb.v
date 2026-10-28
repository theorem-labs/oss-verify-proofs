(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00521d2d4fe8d218 1 1 16 2 37 1 68 1 3 0 1 67 1 69 16P007b223ed1cfd06f 0 5 0 1 45 1 51 1 56 1 57 1P00beb408cc201d8f 0 2 0 1 26 1P00cbf6f52ea57b2b 0 5 0 1 45 1 51 1 56 1 57 1P01bda34bee0d9a72 2 47 1 1 8 3 1 1 60 1 61 1 6 0 2 48 2 54 2 59 2 62 2 63 16 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P020a583786403034 1 1 8 2 0 1 54 1 3 2 1 55 1 56 8P0265bb9f2b0bd5d6 0 5 0 1 46 1 52 1 57 1 58 1P02d0d3e7e3168e5f 0 5 0 1 43 1 49 1 54 1 55 1P03c43b5263024d5e 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P0402fd73bf720453 0 4 0 8 39 8 54 8 55 8P076bade5973d307a 0 5 0 1 45 1 51 1 56 1 57 1P07cfb96105ea1665 0 5 0 1 46 1 52 1 57 1 58 1P089080e56dc9770c 1 1 8 2 0 1 63 1 3 3 1 64 1 65 8P089e0bf7680fbe70 2 47 1 1 8 3 1 1 60 1 61 1 6 0 2 48 2 54 2 59 2 62 2 63 16 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P09176b5dd181bc2c 0 5 0 1 56 1 62 1 67 1 68 1P092fb5262a8cedcd 0 5 0 1 43 1 49 1 54 1 55 1P0999e1724d3c191c 0 2 0 1 26 1P09b2a629711fe854 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P0a63f2ca35a07ce0 0 5 0 1 43 1 49 1 54 1 55 1P0bac0c7ab0078a98 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0c3b25abcdba86eb 0 5 0 1 45 1 51 1 56 1 57 1P0cd4f9ecb2399c41 0 5 0 1 46 1 52 1 57 1 58 1P0d28f6528e22dd20 0 5 0 1 43 1 49 1 54 1 55 1P0f11bea31c441e86 0 2 0 1 25 1P0fd65cae05c0e314 0 5 0 1 46 1 52 1 57 1 58 1P1095b96a634899b4 0 5 0 1 45 1 51 1 56 1 57 1P10bf3cde2a10b8be 0 5 0 1 52 1 58 1 63 1 64 1P12a1562c74c9de4e 0 4 0 16 35 16 67 16 68 16P12ee54c3a8e85cf6 2 63 1 1 8 3 1 1 70 1 71 1 6 0 2 58 2 64 2 69 2 72 2 73 16 1 1 8 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 8P134d8dec8a3ce26d 0 5 0 1 45 1 51 1 56 1 57 1P13856a9636abc388 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P139f7090652a7528 0 5 0 1 45 1 51 1 56 1 57 1P150e2b784540771a 0 5 0 1 45 1 51 1 56 1 57 1P157a0e12975047ed 1 2 16 2 0 1 67 1 16 2 37 1 68 1 2 69 1 70 1P15c5cd7c0c446e8f 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P164a755383c014d4 2 40 1 1 8 3 1 1 57 1 58 1 6 0 2 45 2 51 2 56 2 59 2 60 16 1 1 8 3 2 1 56 1 59 1 4 0 2 57 2 58 2 60 16P169e1005e9c0cbfd 0 5 0 1 46 1 52 1 57 1 58 1P16aa77aaafc9bf9e 2 48 1 1 8 3 1 1 57 1 58 1 6 0 1 45 1 51 1 56 1 59 1 60 8 1 1 8 3 2 1 56 1 59 1 4 0 1 57 1 58 1 60 8P17a10cdb48567fea 0 5 0 1 45 1 51 1 56 1 57 1P18f463d789e52f9c 0 5 0 1 45 1 51 1 56 1 57 1P19aea24df2b4a69b 1 1 8 2 0 1 57 1 3 3 1 58 1 59 8P19bf4d031a9c3c3a 1 1 8 2 0 1 67 1 3 3 1 68 1 69 8P19d5767944a5705b 0 5 0 1 45 1 51 1 56 1 57 1P1a18abfdb4f937c1 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1b5140a37a605ed2 0 4 0 8 48 8 57 8 58 8P1bb7844b34241c74 1 1 16 2 0 1 68 1 3 35 1 67 1 69 16P1c2bcc76b666b24e 0 5 0 1 52 1 58 1 63 1 64 1P1da08542863e1ff5 1 2 16 2 0 1 67 1 16 2 37 1 68 1 2 69 1 70 1P1dd85e89d8b2d570 2 53 1 1 8 3 1 1 66 1 67 1 6 0 2 54 2 60 2 65 2 68 2 69 16 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P1dfa0dca000abe20 2 40 1 1 8 3 1 1 57 1 58 1 6 0 2 45 2 51 2 56 2 59 2 60 16 1 1 8 3 2 1 56 1 59 1 4 0 2 57 2 58 2 60 16P1e4df4421bd2824f 1 1 8 2 0 1 54 1 3 2 1 55 1 56 8P1f48a9cc082691be 2 47 1 1 8 3 1 1 60 1 61 1 6 0 2 48 2 54 2 59 2 62 2 63 16 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2024fac2a055d1d6 0 5 0 1 56 1 62 1 67 1 68 1P202b21bcf749db9d 0 5 0 1 43 1 49 1 54 1 55 1P212fd71a43e6402e 0 4 0 8 39 8 54 8 55 8P214d474f46f85f73 0 4 0 8 48 8 57 8 58 8P21833b542dcdca16 2 40 1 1 8 3 1 1 57 1 58 1 6 0 2 45 2 51 2 56 2 59 2 60 16 1 1 8 3 2 1 56 1 59 1 4 0 2 57 2 58 2 60 16P21bf2c9c39165751 0 5 0 1 45 1 51 1 56 1 57 1P222800bfb5f397fe 0 5 0 1 45 1 51 1 56 1 57 1P22395dbde2098a4a 0 5 0 1 45 1 51 1 56 1 57 1P223c11325fc2f0c4 2 64 1 1 8 3 1 1 70 1 71 1 6 0 1 58 1 64 1 69 1 72 1 73 8 1 1 8 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 8P2419b35f9e04ad8f 0 5 0 1 46 1 52 1 57 1 58 1P2495a4623db51f32 0 5 0 1 45 1 51 1 56 1 57 1P254a9228a21ddae4 0 5 0 1 46 1 52 1 57 1 58 1P25712e340bb3bf7c 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P25b75886eb960652 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P262464ca4df30ff9 1 1 8 2 0 1 57 1 3 3 1 58 1 59 8P2649d66d0e5accbb 0 5 0 1 52 1 58 1 63 1 64 1P267a9e137dc5abeb 0 5 0 1 52 1 58 1 63 1 64 1P267b0b424e9438ed 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P26cfdbe7f0ce304b 0 5 0 1 43 1 49 1 54 1 55 1P272e6b4469857eb9 0 5 0 1 46 1 52 1 57 1 58 1P27449183617bf0cc 0 5 0 1 56 1 62 1 67 1 68 1P28550c4d74277311 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P28621e55c7d18ae0 1 1 16 3 0 1 69 1 70 1 8 37 1 52 1 57 1 58 1 63 1 68 1 71 1 72 16P2873eae1ca8a796c 0 5 0 1 45 1 51 1 56 1 57 1P28a5a0808bf3360e 1 1 8 2 0 1 54 1 3 2 1 55 1 56 8P28ab118b70b2f2e0 0 5 0 1 45 1 51 1 56 1 57 1P28f3b47856ff5944 0 4 0 8 58 8 67 8 68 8P28f9028d6feb23d2 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P2977bab7408ff788 0 5 0 1 45 1 51 1 56 1 57 1P29967490d2a1836d 0 2 0 1 26 1P2acc2b6b02bfba7b 0 4 0 8 48 8 57 8 58 8P2b0071d5b7c9ab16 1 1 8 2 0 1 56 1 3 50 1 57 1 58 8P2b5b77274d51f851 0 5 0 1 52 1 58 1 63 1 64 1P2c7f7a28bd3d0bb4 0 5 0 1 56 1 62 1 67 1 68 1P2ee6504587ffa2ae 0 5 0 1 56 1 62 1 67 1 68 1P2ef0c6f096887eda 0 5 0 1 43 1 49 1 54 1 55 1P2f18abcc47088806 0 4 0 8 54 8 63 8 64 8P3029247734d71f63 0 4 0 8 47 8 56 8 57 8P30546884875be7a7 0 5 0 1 43 1 49 1 54 1 55 1P3245c3671295e194 0 5 0 1 45 1 51 1 56 1 57 1P32670d410972bd8a 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P327fd59704b6b52b 0 5 0 1 52 1 58 1 63 1 64 1P32cd599161dce9ce 0 4 0 16 35 16 67 16 68 16P32d1714a6dbddda4 1 2 16 2 0 1 67 1 16 2 37 1 68 1 2 69 1 70 1P32eeb624b6e045e3 0 5 0 1 52 1 58 1 63 1 64 1P33e6c26814564178 0 5 0 1 45 1 51 1 56 1 57 1P343d7f19969032ac 0 5 0 1 43 1 49 1 54 1 55 1P34cfeb71430f666f 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P354560d6ffd572ce 0 5 0 1 56 1 62 1 67 1 68 1P37bf1cb8f8539438 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3860ad964c443506 2 47 1 1 8 3 2 1 59 1 60 1 6 0 1 47 1 53 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 1 59 1 60 1 62 8P388c1fb5970cc25a 0 4 0 8 39 8 54 8 55 8P38a9ffea6b4f9802 0 5 0 1 52 1 58 1 63 1 64 1P38ae8b867b0d4ea9 0 4 0 8 48 8 56 8 57 8P38f9a644ed1b4c6e 0 5 0 1 56 1 62 1 67 1 68 1P3900083362315c7f 1 1 8 2 0 1 56 1 3 2 1 57 1 58 8P3968d2af76e73b3d 0 5 0 1 45 1 51 1 56 1 57 1P3978ace9ce007748 0 5 0 1 52 1 58 1 63 1 64 1P398993ca94b64f94 2 48 1 1 8 3 1 1 60 1 61 1 6 0 1 48 1 54 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 1 60 1 61 1 63 8P3ab68f72ce57b7cb 1 1 16 3 0 1 69 1 70 1 8 37 1 52 1 57 1 58 1 63 1 68 1 71 1 72 16P3b2258d273346c97 0 5 0 1 45 1 51 1 56 1 57 1P3b3e778e9360c9e6 0 5 0 1 56 1 62 1 67 1 68 1P3be4d11741334440 0 5 0 1 46 1 52 1 57 1 58 1P3c1cd273860c8ebb 2 46 1 1 8 3 2 1 59 1 60 1 6 0 2 47 2 53 2 58 2 61 2 62 16 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3c8bc8a53c368126 1 1 8 2 0 1 57 1 3 3 1 58 1 59 8P3c9322428a6a6858 0 5 0 1 45 1 51 1 56 1 57 1P3e790808e07adce6 0 5 0 1 45 1 51 1 56 1 57 1P3eac1c1c3844c9f6 0 5 0 1 56 1 62 1 67 1 68 1P3f0f180ab9a5a853 1 1 16 3 0 1 69 1 70 1 8 37 1 52 1 57 1 58 1 63 1 68 1 71 1 72 16N000812d85c21fb21N00174cb683c17535N02ac7c6e65b9eb79N02d0c80036b0bb96N050dc5899c21c9c4N055edb505d2efb45N05a314128ad675e0N06061ac78807ca24N089f69e0ef0ca1e2N096f506c48adc955N0b530fe8d9ab2c17N0bac4a7d844db0a7N0d1e88f9261659f9N0e0e4cf32f6f5f9cN0eaad72ba5a05b4fN0efe678d229a487aN0fc4048564599450N107aef0edfbc6ebaN120c13b1e8d4ccdaN1255c00ee5741ffaN1305c86e281f6103N1612d712c080fc8fN16284c28cf07d4bcN1730c41e76834cbbN19d5f2a8cfba7e6aN1a1b37cfdbe8ab0aN1aa502696b555737N1b6f201816bf31c4N1bee076c2bcc1057N1c5506833905d1a4N1e5fcbd0928c99deN1eebf41d79cc09d2N22b7e5ada0ee7c2dN25539f8863a5a9b2N2595b1eb98a70837N275a64c8bf1690c5N287e66d9732bf8beN2be7e0032bb7732bN2c73bda7be5d0593N2ebaaca379587a37N2ed82daf68818604N2f869b4f22f6a2dcN306f271b1b8261ccN31fe1834ff164c16N33641af6d21b8fbbN33989f08ae8c6274N34729a24353b8120N350eefa4c6d09ca5N370da5e375439218N37356c96765deb07N38b6e38c8b36a563N39edaef2868efc5fN3a1f2e4cac1c8070N3ae8e93b35efcc20N3aee8955d974ea1fN3d95bdf00005082aN3da400eaced5744dN3dc2e225f2ca1d06N3e4ae20942ba4936N3e5e8dc50a5af0fdN3f3aa3e2b90364dc"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
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
Ltac2 gd_tbl_A_asn1_seq_cb () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "ASN1_SEQ_CB_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "asn1_seq_cb_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.cshd"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "asn1_seq_cb_stmtA"; "A_ASN1_SEQ_CB"].


Definition A_ASN1_SEQ_CB : Z := 0x09a848.
Notation ASN1_SEQ_CB_STACK_A := 64 (only parsing).      (* [comment removed for export] *)
Definition ASN1_SEQ_CB_PHI : Z := 2 * 32 + AVOL_CALL.  (* [comment removed for export] *)

Definition asn1_seq_cb_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (CTX CURN TAG START LEN : Z) (ct cpad : word) (cl cp cn : Z) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O26.O25.O24.)Lh',(5.O26.O25.O24.)(1.$6.Lr,$6.(7.(8.$0.R13.(9.(:.(;.O20.O1?.O1>.O1=.R12.R11.R10.O1<.O1;.(<.&40.R1.)R?.R>.R=.R<.R;.R:.R9.O1:.O19.O18.O17.O16.O15.O14.O13.O12.O11.R8.R7.R6.R5.)O10.(=.O20.)O?.(>.(2.&40.))R4.(?.O26.))R3.))(7.(10.O26.R4.)(7.(11.O26.R4.O4.(12.&40.O1?.))(7.(13.O1.R3.)(7.(14.O26.O2.R4.)(7.(15.O26.O25.O22.O21.(12.&40.O1?.)(16.O25.)(17.O26.O25.O24.O23.)(18.(19.$6.$6.)(1:.$6.$6.(1;.O>.+8.)(1;.O>.+10.))(18.(19.$6.$6.)(1:.$6.$6.O=.(1;.O=.+20.))(1<.(19.$6.$6.))))O2.R4.)(7.(8.$6.(1=.O26.O25.O24.R2.)(1=.O26.O25.O24.O23.))(7.(8.$6.(17.O26.O25.O24.R2.)(17.O26.O25.O24.O23.))(7.(8.$6.(1>.O26.O25.O24.R2.)(1>.O26.O25.O24.O23.))(7.(1?.O26.O25.O24.R2.R3.)(7.Px,$6.P,(20.O26.O25.O24.O23.R1.)(20.O26.O25.O24.R4.R2.)(7.(21.(22.O26.O25.O24.R2.)(1;.(22.O26.O25.O24.O23.)$23.))(7.(21.(24.O26.O25.O24.R2.)(1;.(24.O26.O25.O24.O23.)(25.O3.)))(26.(7.(8.$6.R1.=)(7.(8.$6.O6.=)(7.(27.O26.O25.O24.R2.O22.O21.R4.)(7.(28.O26.R4.(1;.O>.+8.)(18.$29.(2:.(<.&40.O=.))(1<.$29.)))(1.(2.&40.)Lpad',(2.&40.)(28.O26.R5.O=.(2;.(<.&40.O<.)R1.O:.O;.O5.)))))))(26.(1.$6.LN,$6.(7.(8.$6.R2.=)(7.(2<.(8.$6.O6.=))(7.(8.$6.(2=.R1.+10.)=)(7.(2>.O25.O22.O21.R1.+20.)(7.(26.(21.(1;.R1.+20.)(16.O25.))(21.(17.O26.O25.O24.O23.)R1.))(7.(27.O26.O25.O24.R3.(18.(19.$6.$6.)(1:.$6.$6.R1.+20.)O22.)O21.R5.)(7.(28.O26.R5.(1;.O>.+8.)(18.$29.(2:.(<.&40.R1.))(1<.$29.)))(7.(28.O26.R5.O=.(2;.O9.O8.O7.O6.R1.))(28.O26.R5.R1.(2;.(<.&40.O<.)(<.&40.=)O:.O;.=)))))))))))(7.(8.$6.R1.-6:.)(7.(2<.(8.$6.O6.=))(7.(27.O26.O25.O24.R2.O22.O21.R4.)(7.(28.O26.R4.(1;.O>.+8.)(18.$29.(2:.(<.&40.O=.))(1<.$29.)))(28.O26.R4.O=.(2;.O9.O8.O7.O6.=)))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_seq_cb_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "Ph,(5.O4.O3.O2.)PLB,(2?.$30.)PLF,(2?.$30.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(31.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PCTX,$6.PCURN,$6.PTAG,$6.PSTART,$6.PLEN,$6.Plo,$6.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pcn,$6.Pd,$6.P,(27.O4.O3.O2.R32.R31.R30.R>.)P,(1?.O4.O3.O2.R33.R>.)P,(28.O4.R10.(1;.R>.+8.)(18.$29.(2:.(<.&40.R=.))(1<.$29.)))P,(28.O4.R11.R>.(2;.R9.R8.R7.R6.R5.))P,(8.$6.(2=.(1;.R10.+8.)+8.)=)P,(8.$6.(2=.R10.+8.)=)P,(21.=R12.)P,(32.=R12.)P,(26.(21.(1;.R14.+10.)R13.)(21.(1;.R13.+20.)(1;.R14.+8.)))P,(7.(21.=R13.)(32.R13.(33.+2.+20.)))P,(7.(21.=R13.)(32.R13.(33.+2.+40.)))P,(7.(21.=R13.)(32.R13.(33.+2.+40.)))P,(7.(21.=R?.)(32.R?.(33.+2.+40.)))P,(11.O4.R1;.R14.(12.&40.R3;.))P,(21.(16.O3.)R15.)P,(21.R16.(34.(34.(12.&40.R3=.)+40.)(35.O3.)))P,(21.(12.&40.R3>.)(1=.O4.O3.O2.R42.))P,(8.$6.(2=.(12.&40.R3?.)+10.)=)P,(26.(21.(1;.R1>.+10.)R19.)(21.(12.&40.R40.)(1;.R1>.+8.)))P,(26.(21.(1;.R1>.+20.)R1:.)(21.(12.&40.R41.)R1>.))P,(36.(37.O3.)(38.$30.R45.(39.R44.))R1;.(1=.O4.O3.O2.R46.)(1;.R20.+8.)+8.)P,(36.(37.O3.)(38.$30.R46.(39.R45.))R1<.(1=.O4.O3.O2.R47.)R20.+20.)P,(10.O4.R24.)P,(8.(2.&40.)R43.(<.&40.(3:.O3.)))P,(3;.O4.(3<.O3.)(20.O4.O3.O2.R4:.)R26.(1;.R24.+8.)+8.)P,(3;.O4.(3<.O3.)(20.O4.O3.O2.R4;.)R27.R24.+20.)P,(21.(1;.(22.O4.O3.O2.R4<.)$23.)$3=.)P,(3>.O4.R29.(16.O3.)(17.O4.O3.O2.R4=.)(1;.R27.+8.)(12.&40.R49.)R1<.)P,(21.(1;.(24.O4.O3.O2.R4>.)(25.R1=.))$3?.)P,(8.(2.&40.)R43.(<.&40.R29.))P,(8.(2.&40.)R43.(<.&40.R28.))P,(8.(2.&40.)R43.(<.&40.R28.))P,(8.(2.&40.)R43.(<.&40.R28.))(40.O4.(41.O4.O3.O2.R53.R52.R51.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R2=.R2<.R2;.R2:.R29.R27.R26.R25.R24.R23.R28.R22.R2?.R2>.)(9.(:.(;.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(<.&40.O1.)R30.(>.(2.&40.))R2?.(?.O4.))R2>.))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis CALLOC : arl_calloc R = 0x69484.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.
  Variables (LF : list blk).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32)
            (CTX CURN TAG START LEN lo : Z).
  Hypothesis AL1 : (CTX + 8) mod 8 = 0.
  Hypothesis AL2 : CURN mod 8 = 0.
  Hypothesis CTX0 : 0 <= CTX.
  Hypothesis NZ2 : 0 < CURN.
  Hypothesis D1 : CTX + 16 <= CURN \/ CURN + 32 <= CTX + 8.
  Hypothesis TAGB : 0 <= TAG < 2^32.
  Hypothesis STARTB : 0 <= START < 2^64.
  Hypothesis LENB : 0 <= LEN < 2^64.
  Hypothesis CTXB : CTX + 16 <= 2^64.
  Hypothesis CURB : CURN + 32 <= 2^64.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SPL : lo <= bv_unsigned sp - 64 - arl_need_malloc R.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : CTX + 16 <= lo \/ bv_unsigned sp <= CTX + 8.
  Hypothesis DS2 : CURN + 32 <= lo \/ bv_unsigned sp <= CURN.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  (* [comment removed for export] *)
  Ltac rt_facts hh :=
    pose proof (hcs_ok asegs R HIA hh) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF; pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hh) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ hh ?LBx LF ?mx, TOP : bv_unsigned sp <= htop _ _ _ hh |- _ =>
      pose proof (hm_top asegs R HIA hh LBx LF mx HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange (hcs asegs R HIA hh) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation FRAME := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.   (* [comment removed for export] *)
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.

  (* [comment removed for export] *)
  Lemma cshd_hcs : ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "Phh,(5.$42.VR,VHIA,)PLB0,(2?.$30.)Pmm,P,(2.&40.)(3.(2.&8.))Pc,$6.P,(27.$42.VR,VHIA,R4.R3.VLF,R2.)P,(43.VR,R4.VLF,(16.VR,)(17.$42.VR,VHIA,R5.)R2.)(20.$42.VR,VHIA,R6.R3.)")
(* [comment removed for export] *).
  Proof.
    intros hh LB0 mm c HH [Hs|[(b & Hb & Hr)|[(b & Hb & Hr)|Hc]]].
    - apply (hcs_stack asegs R HIA hh). lia.
    - destruct b as [B j]. eapply (hcs_block asegs R HIA hh LB0 LF mm B j HH Hb). cbn in Hr. lia.
    - destruct b as [B j]. eapply (hcs_fake asegs R HIA hh LB0 LF mm B j HH Hb). cbn in Hr. lia.
    - apply (hcs_static asegs R HIA hh). exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma presA_drop_below : ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "Phh,(5.$42.VR,VHIA,)PLB0,(2?.$30.)PW,(2?.(19.$6.$6.))Pa,$6.Pb,$6.Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))P,(27.$42.VR,VHIA,R8.R7.VLF,R3.)P,(15.$42.VR,R8.VLF,(12.&40.Vsp,)(16.VR,)(17.$42.VR,VHIA,R9.)(18.(19.$6.$6.)(1:.$6.$6.R6.R5.)R7.)R3.R2.)P,(21.R6.(12.&40.Vsp,))P,(21.(16.VR,)R8.)(15.$42.VR,R;.VLF,(12.&40.Vsp,)(16.VR,)(17.$42.VR,VHIA,R<.)R:.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros hh LB0 W a b mm m1 m2 HH [P S] Hb Ha. split; [| exact S].
    pose proof (art_lo asegs R HIA) as ALO.
    flat constr:((hm_apart asegs R HIA hh LB0 LF mm HH)) 2%nat. intros HBR _. rewrite Forall_forall in HBR.
    intros x Hx Hc Ho. apply P; [exact Hx| exact Hc|]. cbn [outside]. split; [| exact Ho].
    intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(bk & Hbk & Hr)]].
    - clear - Hs Hin Hb. lia.
    - clear - Hd1 Hin Ha ALO DHI. cbn in *. lia.
    - apply in_app_iff in Hbk. destruct Hbk as [Hbk|Hbk].
      + destruct (HBR bk ltac:(apply in_app_iff; left; exact Hbk)) as (_ & _ & HC & _). clear - HC Hr Hin Ha ALO. lia.
      + (* [comment removed for export] *)
        assert (HX : exists fb, In fb LF /\ fst fb <= x < fst fb + snd fb).
        { clear - Hbk Hr. induction LF as [|[FB n] r IH]; cbn in Hbk; [destruct Hbk|].
          destruct Hbk as [E|[E|Hbk]].
          - subst bk. cbn in Hr. exists (FB, n). split; [left; reflexivity| cbn; lia].
          - subst bk. cbn in Hr. exists (FB, n). split; [left; reflexivity| cbn; lia].
          - flat constr:((IH Hbk)) 3%nat. intros fb H1 H2. exists fb. split; [right; exact H1| exact H2]. }
        flat constr:(HX) 3%nat. flclear HX. intros fb Hfb Hr2.
        destruct (HBR fb ltac:(apply in_app_iff; right; exact Hfb)) as (_ & _ & HC & _). clear - HC Hr2 Hin Ha ALO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma presA_drop_fresh : ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "Phh,(5.$42.VR,VHIA,)PLB0,(2?.$30.)PW,(2?.(19.$6.$6.))PN,$6.Pk,$6.Pm1,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))P,(15.$42.VR,R6.VLF,(12.&40.Vsp,)(16.VR,)(17.$42.VR,VHIA,R7.)(18.(19.$6.$6.)(1:.$6.$6.R4.(1;.R4.R3.))R5.)R2.R1.)P,(2>.VR,R7.VLF,R5.R4.)(15.$42.VR,R8.VLF,(12.&40.Vsp,)(16.VR,)(17.$42.VR,VHIA,R9.)R7.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros hh LB0 W N k m1 m2 [P S] (F0 & F1 & F2 & F3). split; [| exact S].
    pose proof (art_lo asegs R HIA) as ALO.
    intros a Ha Hc Ho. apply P; [exact Ha| exact Hc|]. cbn [outside]. split; [| exact Ho].
    intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]].
    - clear - Hs Hin F1 ALO LOS SPL NEED0. lia.
    - clear - Hd1 Hd2 Hin F2. cbn in *. lia.
    - destruct b as [B j]. cbn in Hr. pose proof (F3 B j Hb). clear - Hr Hin H. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aevtA_call : ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "PK,P,$4.SpPPmo,P,$4.P,$0.SpPQ,P,$0.SpPms,$44.P,Pmo,$4.P,A1.R5.R1.(40.$42.A1.R5.R2.(9.R3.R2.))P,Pms',$44.Pmo',$4.P,(1.$4.Lmo1,$4.(7.A1.R8.R1.A2.R7.R1.(9.R3.R2.)))(40.$42.R6.(9.R3.R2.))(45.$42.R6.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros K Pmo Q ms HC HK mo Hmo. eapply aevtS_bind; [apply HC, Hmo|].
    intros [ms' mo'] HP. apply HK. exists mo. split; [exact Hmo| exact HP].
  Qed.

  (* [comment removed for export] *)
  Lemma fill_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "Phc,(5.$42.VR,VHIA,)PLBc,(2?.$30.)PND,$6.Pcurv,$6.Pnt,(2.&40.)Pnpad,(2.&40.)Pnl,$6.Pnp,$6.Pnn,$6.Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(27.$42.VR,VHIA,R1:.R19.VLF,R1.)P,(21.(12.&40.Vsp,)(1=.$42.VR,VHIA,R1;.))P,(28.$42.R3.(1;.VCTX,+8.)(18.$29.(2:.(<.&40.R19.))(1<.$29.)))P,(28.$42.R4.R1;.(2;.R19.R18.R17.R16.R15.))P,(8.$6.(2=.R1<.+8.)=)P,(32.=R1=.)P,(21.(1;.R1>.+20.)(33.+2.+40.))P,(26.(21.(1;.VCTX,+10.)R1?.)(21.(1;.R1?.+20.)(1;.VCTX,+8.)))P,(26.(21.(1;.R20.+20.)Vlo,)(21.(12.&40.Vsp,)R20.))P,(36.(37.VR,)(38.$30.R22.(39.VLF,))Vlo,(1=.$42.VR,VHIA,R23.)(1;.VCTX,+8.)+8.)P,(36.(37.VR,)(38.$30.R23.(39.VLF,))Vlo,(1=.$42.VR,VHIA,R24.)R22.+20.)P,(3;.$42.(3<.VR,)(20.$42.VR,VHIA,R25.)R<.(1;.VCTX,+8.)+8.)P,(3;.$42.(3<.VR,)(20.$42.VR,VHIA,R26.)R=.R24.+20.)P,(28.$42.R>.(1;.(12.&40.Vsp,)-40.)(18.$29.(2:.Vs6,)(18.$29.(2:.Vs5,)(18.$29.(2:.Vs4,)(18.$29.(2:.Vs3,)(18.$29.(2:.Vs2,)(18.$29.(2:.Vs1,)(18.$29.(2:.Vs0,)(18.$29.(2:.Vra,)(1<.$29.))))))))))P,(11.$42.R?.Vlo,(1;.(12.&40.Vsp,)-40.))P,(10.$42.R10.)(46.$42.(3<.VR,)(20.$42.VR,VHIA,R2:.)Lms',$44.(1.(2.&40.)Lx5',(2.&40.)(1.(2.&40.)Lx6',(2.&40.)(1.(2.&40.)Lx7',(2.&40.)(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lx28',(2.&40.)(1.(2.&40.)Lx29',(2.&40.)(1.(2.&40.)Lx30',(2.&40.)(1.(2.&40.)Lx31',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(7.(8.$44.R11.(:.(;.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,R=.R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(=.Vra,)Vfc,(>.(2.&40.))R1.(?.$42.)))(7.(47.(18.(19.$6.$6.)(1:.$6.$6.Vlo,(12.&40.Vsp,))(18.(19.$6.$6.)(1:.$6.$6.(1;.VCTX,+8.)(1;.VCTX,+10.))(18.(19.$6.$6.)(1:.$6.$6.R39.(1;.R39.+20.))(1<.(19.$6.$6.)))))R22.R1.)(7.(14.$42.R22.R1.)(7.(10.$42.R1.)(7.(8.(2.&40.)R=.(<.&40.=))(7.(28.$42.R1.(1;.VCTX,+8.)(18.$29.(2:.(<.&40.R39.))(1<.$29.)))(7.(28.$42.R1.R39.(2;.(<.&40.VTAG,)R36.VLEN,VSTART,R33.))(7.(11.$42.R1.Vlo,(12.&40.Vsp,))(27.$42.VR,VHIA,R3;.R3:.VLF,R1.)))))))))))))))))))))))))(:.(;.R21.(<.&40.(1;.(12.&40.Vsp,)-40.))Vgp,Vtp,R20.R1?.R1>.(<.&40.VTAG,)(<.&40.(1;.VCTX,+8.))R1=.R1<.R1;.R1:.R19.R18.R17.R16.(<.&40.VLEN,)(<.&40.VSTART,)(<.&40.R28.)(<.&40.(1;.(48.(1;.VCTX,+8.)+3.)(49.(3<.VR,))))(<.&40.(49.(3<.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R15.R14.R13.R12.)VF,(<.&40.+9:8?<.)Vfc,(>.(2.&40.))R11.(?.$42.)))")
(* [comment removed for export] *).
  Proof.
    intros hc LBc ND curv nt npad nl np nn x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm
           HH TOP HCC HND NDA ND0 NDB DN DSN CW1 CW2 OCC OND FR ST MI.
    rt_facts hc. unfold seq_cells in HND.
    pose proof (munch_refl [(lo, bv_unsigned sp); (CTX + 8, CTX + 16); (ND, ND + 32)] mm) as MU.
    pose proof (wmono_refl asegs mm) as WM.
    pose proof (hm_abase asegs R HIA hc LBc LF mm HH) as AB.
    lx_run_tac (PLAN [] [] 60%N).
    lx_tree.
    lx_post; first [reflexivity | eassumption | idtac].
    all: match goal with |- ?g => idtac "FILL-LEFT:" g end.
    match goal with MU9 : munch ?W mm ?m9 |- _ => eapply (hm_munch asegs R HIA hc LBc LF W mm m9); [exact HH| exact MU9| assumption |] end.
    all: match goal with |- ?g => idtac "HM-LEFT:" g end.
    solve_w_writable.
  Qed.

  (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "Ph,(5.$42.VR,VHIA,)PLB,(2?.$30.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Pcn,$6.Pd,$6.Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)P,(27.$42.VR,VHIA,R>.R=.VLF,R<.)P,(1?.$42.VR,VHIA,R?.R<.)P,(28.$42.R>.(1;.VCTX,+8.)(18.$29.(2:.(<.&40.VCURN,))(1<.$29.)))P,(28.$42.R?.VCURN,(2;.R=.R<.R;.R:.R9.))P,(7.(21.=R;.)(32.R;.(33.+2.+40.)))P,(11.$42.R11.Vlo,(12.&40.Vsp,))P,(21.(12.&40.Vsp,)(1=.$42.VR,VHIA,R14.))P,(36.(37.VR,)(38.$30.R14.(39.VLF,))Vlo,(1=.$42.VR,VHIA,R15.)(1;.VCTX,+8.)+8.)P,(36.(37.VR,)(38.$30.R15.(39.VLF,))Vlo,(1=.$42.VR,VHIA,R16.)VCURN,+20.)P,(10.$42.R15.)P,(3;.$42.(3<.VR,)(20.$42.VR,VHIA,R18.)R16.(1;.VCTX,+8.)+8.)P,(3;.$42.(3<.VR,)(20.$42.VR,VHIA,R19.)R17.VCURN,+20.)P,(21.(1;.(22.$42.VR,VHIA,R1:.)$23.)$3=.)P,(3>.$42.R19.(16.VR,)(17.$42.VR,VHIA,R1;.)(1;.VCTX,+8.)(12.&40.Vsp,)R12.)P,(21.(1;.(24.$42.VR,VHIA,R1<.)(25.R13.))$3?.)(40.$42.(41.$42.VR,VHIA,R1=.R1<.VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VCTX,VCURN,VTAG,VSTART,VLEN,R19.R18.R17.R16.R15.Vlo,R14.R1;.R1:.)(9.(:.(;.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(<.&40.VCTX,)(<.&40.VTAG,)(<.&40.VSTART,)(<.&40.VLEN,)R13.R12.R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(<.&40.+9:848.)Vfc,(>.(2.&40.))R1;.(?.$42.))R1:.))")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo ct cpad cl cp cn d a4 a5 a6 a7 HH HKmo HCC HCUR CPB ST TOP CW1 CW2 MI OCC OCUR BUD UW BUDF.
    pose proof (conj HH I) as HH0.   (* [comment removed for export] *)
    rt_facts h.
    pose proof (fr_charge_nonneg _ _ _ _ _ _ _ UW) as FRC0.
    pose proof (hstkhi_le64 asegs R HIA h ltac:(clear - LOS SPL SPR NEED0; lia)) as TOP64.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
        pose proof (munch_refl [(lo, bv_unsigned sp); (CTX + 8, CTX + 16); (CURN, CURN + 32)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold seq_cells in HCUR.
    assert (CTXP : 0 < CTX).
    { pose proof OCC as CR. apply aobj_crange in CR.
      assert (HY : hcs asegs R HIA h (CTX + 8 - (CTX + 8) mod 64)).
      { eapply (hcs_hull64 asegs R HIA h (CTX + 8)); [apply CR; lia| pose proof (Z.mod_pos_bound (CTX + 8) 64 ltac:(lia)); lia]. }
      destruct (hcs_app asegs R HIA h (CTX + 8 - (CTX + 8) mod 64) 1
                  ltac:(intros x Hx; replace x with (CTX + 8 - (CTX + 8) mod 64) by lia; exact HY) ltac:(lia)) as [[H0 _]|[H0 _]].
      - clear - H0 CTX0. pose proof (Z.mod_pos_bound (CTX + 8) 64 ltac:(lia)). pose proof (Z.div_mod (CTX + 8) 64 ltac:(lia)). nia.
      - clear - H0 SB64 CTX0. lia. }
    (* [comment removed for export] *)
    clear MU. lx_run_tac (PLAN [0x69484] [] 80%N). lx_tree.
    { (* [comment removed for export] *)
      match goal with H : munch ?W' m ?mx |- _ => rename mx into m9; rename H into MU9;
        assert (MU9' : munch [(lo, bv_unsigned sp); (CTX + 8, CTX + 16); (CURN, CURN + 32)] m m9)
          by (eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear - SPL NEED0; intros x Hx; lia) end.
      match goal with H : wmono _ m m9 |- _ => rename H into WM9 end.
      apply aevtA_done. intros mo' [HK' MF'].
      lx_exs; lx_ands; [> reflexivity | ..]; try assumption; try reflexivity; try assumption.
      - (* [comment removed for export] *)
        eapply (presA_drop_below h LB _ lo (bv_unsigned sp) m); [exact (proj1 HH0)| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m9 (hcs asegs R HIA h) CSOK);
          [| intros c Hc; exact (cshd_hcs h LB m c (proj1 HH0) Hc) | exact MU9' | exact WM9 ].
        unfold w_client. repeat (apply Forall_cons; [cbn [fst snd]; solve_crange|]). apply Forall_nil.
      - intros y Hy; exact Hy.
      - unfold ASN1_SEQ_CB_PHI, AVOL_CALL; clear; lia.
      - clear - FRC0; lia.
      - left. lx_ands; try assumption; try reflexivity.
        + lx_lia.
        + (* [comment removed for export] *)
          eapply (hm_munch asegs R HIA h LB LF _ m m9); [exact (proj1 HH0)| exact MU9'| exact WM9| solve_w_writable].
        + eexists; eassumption.
      all: match goal with |- ?g => idtac "CP0-LEFT:" g end. }
    (* [comment removed for export] *)
    clear ST HCC HCUR OCC OCUR MI.
    match goal with H : munch _ m ?mx |- _ => rename mx into m1; rename H into MU0 end.
    match goal with H : wmono _ m m1 |- _ => rename H into WM end.
    match goal with H : rw_cells _ m1 (bv_unsigned sp + -64) _ |- _ => rename H into FR end.
    match goal with H : stk _ m1 lo (bv_unsigned sp + -64) |- _ => rename H into ST end.
    assert (MU : munch [(lo, bv_unsigned sp); (CTX + 8, CTX + 16); (CURN, CURN + 32)] m m1)
      by (eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto).
    assert (KZ : cp <> 0) by lx_lia.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    (* [comment removed for export] *)
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := 1) (sz := 32) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; rewrite ?(unsigned_lit (CTX + 8)) by qlia; try eassumption; try reflexivity; try qlia.
      all: try c24_lit.   (* [comment removed for export] *)
      all: try (rewrite (unsigned_lit TAG) by (clear - TAGB; lia); apply uwc_data; [eapply uwc_nonneg; exact UW | clear - TAGB LOS ALO; pose proof alloc_ceiling_lo; lia]).
      all: try (eapply (hm_munch asegs R HIA h LB LF _ m m1); [exact (proj1 HH0)| exact MU0| exact WM| solve_w_writable]).
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    clear MU0.
    intros ms' mo' (mo1 & [HK1 MF1] & PO).
    flat constr:(PO) 4%nat. flclear PO. intros ms2 mo2 E PO. injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by qlia.
    flat constr:(PO) 14%nat. flclear PO. intros MI2 ST2 MF2 WM2 HP2 h2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 CASES.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    (* [comment removed for export] *)
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2.
    (* [comment removed for export] *)
    assert (HPX : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(CTX + 8, CTX + 16); (CURN, CURN + 32)] m m2).
    { eapply presA_trans.
      - eapply (presA_drop_below h LB _ lo (bv_unsigned sp) m); [exact (proj1 HH0)| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 (hcs asegs R HIA h) CSOK);
          [| intros c Hc; exact (cshd_hcs h LB m c (proj1 HH0) Hc) | exact MU | exact WM].
        unfold w_client. repeat (apply Forall_cons; [cbn [fst snd]; solve_crange|]). apply Forall_nil.
      - eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SPL NEED0; lia| clear - LOS SPL NEED0; lia| clear; lia| intros y _; exact I]. }
    assert (WMX : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU WM HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    (* [comment removed for export] *)
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    repeat match goal with H : aobj _ _ (hcs _ _ _ h) _ _ _ |- _ => apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in H end.
    clear CSOK SB64 SCS0 SCS HTOP. rewrite <- HT2 in CW1, CW2, TOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_stack asegs R HIA h2) as SCS0.
    destruct CASES as [[E0 HH2] | (N & E0 & HREST)]; match type of E0 with ?v = _ => subst v end.
    - (* [comment removed for export] *)
      pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      pose proof (munch_refl [(lo, bv_unsigned sp); (CTX + 8, CTX + 16); (CURN, CURN + 32)] m2) as MU.
      pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      lx_run_tac (PLAN [] [] 40%N). lx_tree.
      match goal with H : munch _ m2 ?mx |- _ => rename mx into m9; rename H into MU9 end.
      match goal with H : wmono _ m2 m9 |- _ => rename H into WM9 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      lx_exs; lx_ands; [> reflexivity | assumption | assumption | exact MF9 | eapply wmono_trans; [exact WMX| exact WM9] | 
        | exact HT2 | exact HS2 | exact HF2 | exact HK9 | exact HCS2 | exact HV2 | exact HFR2 | ].
      + (* [comment removed for export] *) eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_drop_below h2 LB _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
          [| intros c Hc; exact (cshd_hcs h2 LB _ c HH2 Hc) | exact MU9 | exact WM9].
        unfold w_client. repeat (apply Forall_cons; [cbn [fst snd]; solve_crange|]). apply Forall_nil.
      + right; right. lx_ands; try assumption; try reflexivity.
        eapply (hm_munch asegs R HIA h2 LB LF _ m2 m9); [exact HH2| exact MU9| exact WM9| solve_w_writable].
      all: match goal with |- ?g => idtac "FAIL-LEFT:" g end.
    - (* [comment removed for export] *)
      flat constr:(HREST) 5%nat. flclear HREST. intros HN16 HFR HNS HH2 HNEW.
      change (1 * 32) with 32 in HFR, HNS, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul repeat] in HNEW.
      apply (rw_cells_zeros asegs m2 N 32 (seq_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0)) in HNEW; [| cbn; repeat split; reflexivity | reflexivity].
      unfold seq_cells in HNEW.
      pose proof (hm_top asegs R HIA h2 ((N, 32) :: LB) LF m2 HH2) as HTOP.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
      assert (HINN : In (N, 32) (((N, 32) :: LB) ++ fdata LF)) by (left; reflexivity).
      pose proof (hm_aobj_block asegs R HIA h2 ((N, 32) :: LB) LF m2 N 32 HH2 (or_introl eq_refl)) as ON.
      pose proof (client_wrange_block L (((N, 32) :: LB) ++ fdata LF) lo (htop asegs R HIA h2) N 32 N 32 HINN ltac:(lia) ltac:(lia)) as CWN.
      flat constr:(HFR) 4%nat. intros HN0 HNC HND HNAP.
      assert (APC : N + 32 <= CTX + 8 \/ CTX + 8 + 8 <= N).
      { eapply (fresh_apart_client R LB LF lo (CTX + 8) 8 N 32 HFR); [| clear; lia| clear; lia| clear - ALO LOS; lia].
        eapply client_range_inside; [exact CW1| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (APU : N + 32 <= CURN \/ CURN + 32 <= N).
      { eapply (fresh_apart_client R LB LF lo CURN 32 N 32 HFR); [| clear; lia| clear; lia| clear - ALO LOS; lia].
        eapply client_range_inside; [exact CW2| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (APS : N + 32 <= lo \/ bv_unsigned sp <= N) by (clear - HNC ALO LOS; lia).
      assert (NHI : N + 32 <= 2^64) by (clear - HN0 HNC; pose proof (alloc_ceiling_val R); lia).
      (* [comment removed for export] *)
      apply (client_wrange_mono L _ (((N, 32) :: LB) ++ fdata LF)) in CW1; [| intros b Hb; right; exact Hb].
      apply (client_wrange_mono L _ (((N, 32) :: LB) ++ fdata LF)) in CW2; [| intros b Hb; right; exact Hb].
      pose proof (munch_refl [(lo, bv_unsigned sp); (N, N + 32); (CTX + 8, CTX + 16); (CURN, CURN + 32)] m2) as MU.
      pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      lx_run_tac (PLAN [] [] 60%N). lx_tree.
      match goal with H : munch _ m2 ?mx |- _ => rename mx into m9; rename H into MU9 end.
      match goal with H : wmono _ m2 m9 |- _ => rename H into WM9 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      lx_exs; lx_ands; [> reflexivity | assumption | assumption | exact MF9 | eapply wmono_trans; [exact WMX| exact WM9] | 
        | exact HT2 | exact HS2 | exact HF2 | exact HK9 | exact HCS2 | exact HV2 | exact HFR2 | ].
      + (* [comment removed for export] *)
        eapply presA_trans; [exact HPX|]. rewrite <- HS2.
        eapply (presA_drop_fresh h2 LB _ N 32); [| exact HFR].
        eapply (presA_weaken asegs R ((N, 32) :: LB) LB LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2)
                  [(N, N + 32); (CTX + 8, CTX + 16); (CURN, CURN + 32)]);
          [| intros b Hb; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below h2 ((N, 32) :: LB) _ lo (bv_unsigned sp) _); [exact HH2| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R ((N, 32) :: LB) LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
          [| intros c Hc; exact (cshd_hcs h2 _ _ c HH2 Hc) | | exact WM9].
        * unfold w_client. repeat (apply Forall_cons; [cbn [fst snd]; solve_crange|]). apply Forall_nil.
        * eapply munch_weaken; [| exact MU9]. clear. intros z Hz; clear - Hz; cbn [outside] in *. tauto (* [comment removed for export] *).
      + right; left. exists N. lx_ands; try assumption; try reflexivity.
        all: match goal with |- ?g => idtac "FRESH-GOAL:" g end.
        eapply (hm_munch asegs R HIA h2 ((N, 32) :: LB) LF _ m2 m9); [exact HH2| exact MU9| exact WM9| solve_w_writable].
      all: match goal with |- ?g => idtac "FRESH-LEFT:" g end.
  Qed.
End Walk.

Lemma A_asn1_seq_cb_spec : ltac2:(CDefT.buildp (gd_tbl_A_asn1_seq_cb ()) "PR,$4:.PHIA,(4;.$42.R1.)P,(4<.(3<.R2.))P,(8.$6.(4=.R3.)+69484.)P,(21.=(35.R4.))P,(21.(4>.(37.R5.))(4?.(37.R5.)))(50.$42.R6.R5.$51.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG CAL NEED0 DHI. unfold asn1_seq_cb_stmtA, A_ASN1_SEQ_CB.
  intros until d. intros HH HK HCC HCUR AL1 AL2 CTX0 NZ2 D1 TAGB STARTB LENB CPB ST LOS SLO TOP SPA DS1 DS2 CW1 CW2 MI TPV OCC OCUR BUD UW BUDF -> -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HCC) as CCB. pose proof (rw_cells_bound _ _ _ _ HCUR) as CUB.
  cbn [seq_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in CCB, CUB.
  eapply main_walk; try eassumption; try lia.
Qed.


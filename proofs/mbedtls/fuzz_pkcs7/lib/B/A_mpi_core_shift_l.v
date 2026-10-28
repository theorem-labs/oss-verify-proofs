(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_shift_l.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00cc9d9001177f98 0 2 0 1 1 1P022355a801ea253b 0 2 0 1 2 1P0251af59d91e3491 1 1 16 7 0 4 33 16 49 16 50 16 52 4 71 4 72 4 2 53 1 73 1P028353fb09d9f41f 0 2 0 1 70 1P02b0812a3445b1c3 2 46 1 1 4 3 3 1 62 1 63 1 6 0 1 48 1 54 1 61 1 64 1 65 4 1 1 4 3 2 1 61 1 64 1 4 0 4 62 4 63 4 65 16P02d4682a6e2c3ed8 0 5 0 1 44 1 51 1 56 1 57 1P038f5d02e14faa30 1 1 16 7 0 4 45 4 50 16 51 4 53 16 69 4 70 4 3 32 1 49 1 71 1P03b53929923a5eff 0 7 0 4 32 16 49 16 50 16 51 4 71 4 72 4P04346bcc3c043563 0 2 0 1 9 1P044b8daf8883c5fd 0 2 0 1 61 1P050ea5ed47c0b4f8 0 3 0 1 23 1 37 1P052419456438db71 0 6 0 1 45 1 46 1 51 1 58 1 59 1P0597128f12b522d2 0 8 0 4 31 16 44 4 47 16 48 16 50 4 67 4 68 4P0609df7ff9624ccc 0 5 0 4 31 16 48 4 70 4 71 4P06cd72832d05ee66 0 2 0 1 23 1P06efac0e1f2dd139 0 4 0 1 44 1 58 1 59 1P076fbe9cd7f30a1d 0 2 0 1 2 1P07d6849b5935bd55 0 2 0 1 21 1P086a2ca7db717304 0 2 0 1 26 1P095e1c3a1b558e3c 0 3 0 1 19 1 28 1P09687454a33d1b23 0 7 0 4 33 16 50 16 51 16 52 4 70 4 71 4P09926de6b2d04429 0 8 0 4 34 16 47 4 50 16 51 16 53 4 70 4 71 4P09c5c0f894135c90 0 3 0 1 19 1 28 1P09e0e350d6c562a6 0 3 0 1 23 1 37 1P09e26ab78e39b644 0 6 0 1 45 1 46 1 51 1 58 1 59 1P09f3ec2d179a5de1 0 4 0 32 19 1 24 1 46 1P09f454d6ce099d5f 0 7 0 4 32 16 49 16 50 16 51 4 71 4 72 4P0a00c9ca6a47a1a6 0 7 0 4 32 16 49 16 50 16 51 4 71 4 72 4P0ab34a77e0f018a7 0 5 0 4 29 16 46 4 66 4 67 4P0ad0337b7ad2f597 0 2 0 1 60 1P0bae5b335409d4ba 0 2 0 1 5 1P0c0e9c47cb4a1c35 0 2 0 1 24 1P0c27508fd4545310 0 2 0 1 1 1P0c2f8e0c71b079a0 1 1 16 7 0 4 46 4 51 16 52 4 54 16 70 4 71 4 3 33 1 50 1 72 1P0cdd36851b02aea7 0 2 0 1 10 1P0dd692db5725efea 0 3 1 1 46 1 54 4P0df074398cfa5e7b 0 4 0 32 18 1 23 1 45 1P0edce6b109a82a83 0 2 0 1 53 1P0f16665125a22c06 1 1 16 7 0 4 33 16 49 16 50 16 52 4 71 4 72 4 2 53 1 73 1P0f3d5f8f157b1bf3 0 5 0 1 45 1 51 1 58 1 59 1P0fd2600a085d1ed2 0 2 0 1 1 1P10882e33d835ffa0 0 5 0 1 45 1 51 1 58 1 59 1P10d5f146e09bf8bb 1 1 32 3 17 1 21 1 44 1 9 0 4 14 1 15 1 24 4 36 4 38 1 39 1 48 4 62 4P10da35dcf23dd8be 0 2 0 1 29 1P11840e7981880b1e 0 2 0 1 2 1P11baa448a03f4184 0 2 0 1 25 1P128a67c11ffd62c1 0 2 0 1 29 1P13833f077fb77502 0 2 0 1 60 1P13c9c0e5c47c11a0 0 6 0 1 45 1 46 1 51 1 58 1 59 1P15cae6ca5a8bb202 0 2 0 1 1 1P163f1b53f91375e7 0 4 0 1 44 1 58 1 59 1P164db7aa3a657c26 0 2 0 1 2 1P16a16ddb7fcf226f 0 2 0 1 4 1P17b3a929c5f19c04 0 2 0 1 8 1P1849648c0563afc1 0 2 0 1 25 1P18b21256d16163a1 0 2 0 1 1 1P18e2805a6ed4054f 0 2 0 1 60 1P19ec0ed206257454 0 9 0 4 25 1 26 1 32 4 49 8 50 4 51 1 52 1 61 4P1a304e8940bccda1 0 5 0 1 45 1 51 1 58 1 59 1P1a497526b37a11ce 2 46 1 1 4 3 3 1 62 1 63 1 6 0 1 48 1 54 1 61 1 64 1 65 4 1 1 4 3 2 1 61 1 64 1 4 0 4 62 4 63 4 65 16P1a4ff85f851b173e 0 5 0 1 44 1 51 1 56 1 57 1P1a5d95713f825468 0 5 0 1 45 1 51 1 58 1 59 1P1a8019be80024e5a 0 5 0 1 44 1 51 1 56 1 57 1P1b0cb46ad58eeddb 0 5 0 1 45 1 51 1 58 1 59 1P1bbaca73c44d4ad3 0 9 0 4 30 16 43 4 47 16 48 16 49 4 51 16 67 4 68 4P1bf42a12f80ce86a 0 2 0 1 25 1P1d6928f8a1f6efeb 0 4 0 1 44 1 58 1 59 1P1d7346ebc68d0940 0 2 0 1 22 1P1e1ff77d20a43717 0 2 0 1 5 1P1e70521198df0264 0 6 0 1 45 1 46 1 51 1 58 1 59 1P1f8aa2c799a8be55 0 6 0 1 45 1 46 1 51 1 58 1 59 1P1f942ff6313830a8 0 2 0 1 2 1P1fb85325e1cbed05 0 4 0 1 44 1 58 1 59 1P1ffc1fe9c662c0ff 1 1 32 3 25 1 29 1 54 1 6 0 4 32 16 49 4 70 4 71 4 72 16P2090471b96d79242 0 2 0 1 4 1P20c6a92460d81001 0 5 0 1 45 1 51 1 58 1 59 1P20c82833dfd3fd0f 0 8 0 4 33 16 46 4 49 16 50 16 52 4 69 4 70 4P20ce43c8eeacfc52 0 8 0 4 31 16 44 4 47 16 48 16 50 4 67 4 68 4P2135127128aea8c3 1 1 32 3 26 1 30 1 55 1 6 0 4 33 16 50 4 69 4 70 4 71 16P214c1b16bb36c173 0 5 0 1 45 1 51 1 58 1 59 1P21f8dc83e6342a72 1 1 32 3 17 1 21 1 44 1 6 0 4 24 16 39 4 62 4 63 4 64 16P225b2c7be0e2acde 0 4 0 32 22 1 27 1 58 1P2291916fe9019751 0 5 0 4 29 16 46 4 66 4 67 4P22b8dc941a8a9a8f 1 1 16 7 0 4 33 16 49 16 50 16 52 4 71 4 72 4 2 53 1 73 1P23fa9cb5388f7ceb 2 46 1 1 4 3 3 1 62 1 63 1 6 0 1 48 1 54 1 61 1 64 1 65 4 1 1 4 3 2 1 61 1 64 1 4 0 4 62 4 63 4 65 16P24715c2724a8ac85 0 4 0 32 19 1 24 1 48 1P252430da4f31dce3 0 2 0 1 2 1P25253060fa69a668 0 2 0 1 1 1P25422363153cd06d 0 2 0 1 69 1P262d355dc243a119 0 2 0 1 1 1P26565430e25699d7 0 2 0 1 21 1P2684d180f2467c5c 1 1 32 3 23 1 27 1 52 1 6 0 4 30 16 47 4 66 4 67 4 68 16P269e8d5e6c0e93e0 0 2 0 1 20 1P27571057f81434e1 0 2 0 1 2 1P287ea9f04321bd5c 1 1 32 3 23 1 27 1 52 1 6 0 4 30 16 47 4 66 4 67 4 68 16P29e161724498a9f4 0 5 0 1 44 1 51 1 56 1 57 1P2b65c52562ef6e90 0 2 0 1 8 1P2b83af2dd3589d5a 0 2 0 1 1 1P2bb30c6c1994302d 0 2 0 1 1 1P2c29f34cdbff6534 0 5 0 1 45 1 51 1 58 1 59 1P2c489b0f670d3914 0 2 0 1 2 1P2c6d19451163a78c 0 4 0 1 44 1 58 1 59 1P2d62eea44e3f1f62 0 2 0 1 2 1P2d95bc47a3046648 0 4 0 1 44 1 58 1 59 1P2dea5ffb9e8fa14b 2 46 1 1 4 3 3 1 62 1 63 1 6 0 1 48 1 54 1 61 1 64 1 65 4 1 1 4 3 2 1 61 1 64 1 4 0 4 62 4 63 4 65 16P2e1062f1ea189251 1 1 16 7 0 4 34 16 50 16 51 16 53 4 70 4 71 4 2 54 1 72 1P2e3910a202be1929 2 46 1 1 4 3 3 1 62 1 63 1 6 0 1 48 1 54 1 61 1 64 1 65 4 1 1 4 3 2 1 61 1 64 1 4 0 4 62 4 63 4 65 16P2e655628e3a50c06 0 5 0 1 45 1 51 1 58 1 59 1P2f051a5a895cc9a7 0 3 0 1 23 1 37 1P2ff4baabc8c4fe97 0 6 0 1 45 1 46 1 51 1 58 1 59 1P3042d5cf05927a14 0 2 0 1 70 1P3052877e50c28bf2 0 5 0 1 44 1 51 1 56 1 57 1P30c073a186bac696 2 43 0 9 0 1 1 1 25 4 40 1 44 1 50 4 51 1 64 1 65 1 1 1 32 3 19 1 23 1 46 1 7 0 16 2 16 26 64 41 16 64 16 65 16 66 64P34e455454b7e4d30 0 5 0 1 44 1 51 1 56 1 57 1P358cadc249b03c12 0 2 0 1 1 1P35c304b6543ac7db 0 5 0 4 32 16 49 4 69 4 70 4P361ce4e3c9bb76b2 0 5 0 4 23 16 38 4 62 4 63 4P363f2c8f7ebafb71 1 1 32 3 17 1 21 1 44 1 9 0 4 14 1 15 1 24 4 36 4 38 1 39 1 48 4 62 4P36a0051350e2fd16 0 2 0 1 61 1P36deb5d34a2df561 0 5 0 1 44 1 51 1 56 1 57 1P36e282332d75a12d 0 5 0 1 45 1 51 1 58 1 59 1P37e1798dd401037e 2 57 0 11 0 1 1 1 34 4 51 4 52 4 53 1 57 1 63 4 64 1 73 1 74 1 1 1 4 8 0 1 2 1 35 4 51 4 52 4 54 1 73 1 74 1 2 55 1 75 1P3833a038660dfd89 0 5 0 1 45 1 51 1 58 1 59 1P3c2b32d84bd0fbb4 0 9 0 4 30 16 43 4 47 16 48 16 49 4 51 16 67 4 68 4P3cb7afea2e2129a1 0 4 0 32 18 1 23 1 45 1P3d0e9ac8bf86a627 0 4 0 1 33 1 50 1 53 1P3da0bf9e74b39830 0 2 0 1 29 1P3e7b9fc6833f5505 0 2 0 1 69 1P3ebb1f8f5e19064f 2 46 1 1 4 3 3 1 62 1 63 1 6 0 1 48 1 54 1 61 1 64 1 65 4 1 1 4 3 2 1 61 1 64 1 4 0 4 62 4 63 4 65 16P3efe88d479084032 0 5 0 1 45 1 51 1 58 1 59 1P3fa3ae26e84f529f 0 2 0 1 8 1P3fb34b4144afc994 0 2 0 1 20 1N000806998de33c6dN01101b0b5e7e4054N018897fba06892a4N02d3e9a492664518N0313134819ba25c0N0350c0245b3f2455N0589e76f9b64413bN05f905fd453dfd5fN07307f98f62bf63bN07ec6e7e6619a473N087f3896a8dbbfeeN089d231d6ba4c909N08cf14d9761a0effN091282f2cb37251bN0a965dc5c77e948bN0ac9fcb5847994f0N0b40dfb0751e8844N0bb7e4873f15d6d4N0c1ae4d27a8f0b80N0c1b89fcb6dbeba7N0ccf014f97e7c7d4N0ce18a6a875da8c9N0ced004cb45864b2N0d80216f98315c2dN0e4c51ba97cac740N0e87e61dd9a4edfdN0fb442c509e7c3f3N0fb67d9bfec2da23N105483aa3f83fffdN109ba9bfdb7cb2aaN10d22f0a52eb01e6N1259ef8ed8c3e4bfN1264acf65e279cc6N127c8d5f2630a6e3N12ce3a8799ab41f8N12d3d9d6cc0af35bN12d745fd85a71daeN13eadb4e64cc71ebN148ec7e8117c0cbeN14c647b222801579N15d8ea22c2cade18N167ac5b26fc31e28N1695f3809348f86dN16d859c52ae158a6N16e20236a547b8b1N17641dea00e1da20N177023a94d0d1cffN17a7ae2946c163c7N17da3a5a056b570cN1940c4372c5c916dN195baaba792deeb4N1a2ccbd69bd2649cN1a2e388fe2fda31eN1c6c0ec171bc1266N1d168b823aeb0c61N1d2628e74cb5fa4eN1dfd6bf130c73e49N1e40c1c5be994269N1f768d11848d442dN2109dfe53d9c9862N211863ff1c79cad1N2153837d40e788c2N2244bb4cfbcb221cN23f62aeb93d9d348N2512948a6ac93142N25c54f0512d22f52N25dcb5b0b315b34fN2673fd56fe25db62N2756709cd50403eaN2774bdf32fe92f54N27e9f09cb6c3e4a3N287032cfaad882f2N2a0929871d93b12aN2a1bb5f6a05ece95N2ab51a3f554877b3N2b7743d74c7067ceN2c987497f99389f7N2e0b046e028314bbN2e715857584ebedfN2e9330b37f3d675aN2efee47b4a281442N2f6fc81d7eb070caN307b8804520342dcN30d7b917dacc2ba1N30d9add64bd0760aN31525ef7221d2a82N3177075b31aed966N31cd96d4dcdb6844N320d60e70b6438daN32403fbfa1b2573eN34502fecc2f26042N352e6edf781d83acN37090393dedbcaaeN37211705142d063aN37a8641dadee331fN37d8e80a87a29f4aN38901ff4a1fd56e1N39f333be3ee60919N3a8318c072cdfb16N3caa19a216fdf3eaN3dac7b1247464d11N3e8d3a9d55953764N3ed07923d8a91435"%lxh.
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
Ltac2 gd_tbl_A_mpi_core_shift_l () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_SHIFT_L_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_shift_l_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lseg"; "Corelib.Init.Peano.le"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_shift_l.shl_inv"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.w32"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_shift_l.ltp2"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_shift_l.shl_vz"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "Corelib.Init.Nat.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "A_ASAN_MEMSET_SL"; "mpi_core_shift_l_stmtA"; "A_MPI_CORE_SHIFT_L"].


Definition A_MPI_CORE_SHIFT_L : Z := 0xa4418.   (* [comment removed for export] *)
Definition A_ASAN_MEMSET_SL : Z := 0x68258.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition MPI_CORE_SHIFT_L_STACK_A : Z := 48.

Definition mpi_core_shift_l_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n cnt : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_shift_l ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(9.O18.)O7.(:.(2.&40.))R2.(;.O1>.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O6.(11.O6.(12.+4.O5.)))(=.(>.$?.$?.)(10.$?.$?.O2.(13.&40.O17.))(14.(>.$?.$?.))))O1.R2.)(5.(15.O1>.O1.R2.)(5.(16.O1>.R2.)(5.(17.O1>.R2.O6.R1.)(5.(6.$18.(19.(2.&40.)R1.)(19.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1:.(2.&40.)(1;.O5.)R1.)(1:.(2.&40.)(1;.O5.)O3.))(5.(6.$?.(1<.R1.O5.)(1=.(12.(1<.O3.O5.)(1>.+2.O4.))(1>.+2.(12.+20.O5.))))(5.(1?.O1>.R2.O2.(13.&40.O17.))(20.O1>.O1=.O1<.O1;.O1:.O19.R2.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_shift_l_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_shift_l ()) "Ph,(21.O4.O3.O2.)PLB,(4.$22.)PLF,(4.$22.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.Pn,$?.Pcnt,$?.Plo,$?.Pxs,(4.(2.&40.))P,(20.O4.O3.O2.R2:.R29.R28.R6.)P,(17.O4.R7.R6.R2.)P,(5.(24.=R6.)(24.R6.+2710.))P,(24.R7.(25.(19.(2.&40.)R4.)))P,(5.(24.=R7.)(26.R7.(1>.+2.+40.)))P,(6.$?.(1=.R:.+4.)=)P,(27.(6.$?.R:.=)(26.=R;.))P,(26.R<.(1>.+2.+40.))P,(1?.O4.R>.R:.(13.&40.R2>.))P,(24.(28.O3.)R;.)P,(24.R<.(29.(29.(13.&40.R30.)$2:.)(2;.O3.)))P,(24.(13.&40.R31.)(2<.O4.O3.O2.R35.))P,(6.$?.(1=.(13.&40.R32.)+10.)=)P,(27.(24.(11.R12.(12.+4.(25.(19.(2.&40.)R>.))))R?.)(24.(13.&40.R33.)R12.))P,(2=.(2>.O3.)(2?.$22.R37.(30.R36.))(28.O3.)(2<.O4.O3.O2.R38.)R13.(12.+4.R12.))P,(16.O4.R15.)P,(6.$?.(1=.(13.&40.R37.)+2.)=)P,(31.O4.(32.O3.)(33.O4.O3.O2.R3;.)R17.R16.(12.+4.R15.))P,(6.(2.&40.)R30.(34.&40.R17.))P,(6.(2.&40.)R30.(34.&40.R17.))P,(6.(2.&40.)R30.(34.&40.R17.))(35.O4.(32.O3.)(33.O4.O3.O2.R3?.)(36.O4.O3.O2.R3?.R3>.R3=.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R1:.R19.R18.R16.R17.R1;.)(7.(8.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(34.&40.O1.)R1<.(:.(2.&40.))R1;.(;.O4.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Ltac shadow_chk_x H xn n :=
  try unfold mkR;
  lazymatch goal with |- _ (MS ?R _ _ _ _ _ _) =>
    let v := getx R xn in
    lazymatch v with
    | Z_to_bv 64 (Z.shiftr ?c 3 + _) => shadow_chk H c n
    | Z_to_bv 64 (_ + Z.shiftr ?c 3) => shadow_chk H c n
    end
  end.

Lemma shl_zero_step : forall (y0 tl : list word) (j r : nat), (S j <= length y0)%nat ->
  upd (firstn (S j) y0 ++ repeat (Z_to_bv 64 0) r ++ tl) j (Z_to_bv 64 0) = firstn j y0 ++ repeat (Z_to_bv 64 0) (S r) ++ tl.
Proof.
  induction y0 as [|a y0 IH]; intros tl j r Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [reflexivity|].
  cbn [firstn app upd]. rewrite IH by lia. reflexivity.
Qed.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_SL.
  Hypothesis NEED0 : 0 <= arl_need_amem R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (s0 s1 s2 s3 s4 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n cnt v0 v1 lx lo : Z) (xs0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 0 <= X /\ X + 4 * lx <= 2^64.
  Hypothesis NZX : n = 0 \/ 0 < X.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis Hcnt : 0 <= cnt < 2^64.
  Hypothesis Ecnt : cnt = 32 * v0 + v1.
  Hypothesis Rv : 0 <= v0 /\ 0 <= v1 < 32.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 48 - arl_need_amem R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X (4 * n).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    match goal with HH : HM _ _ _ h LB LF _ |- _ =>
      pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

  Notation POST := (mpi_core_shift_l_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cnt xs0 lo m).
  Notation W := [(X, X + 4 * n); (lo, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation DINV mm ys := (u32arr asegs mm X ys /\ length ys = length xs0
                          /\ munch W m mm /\ wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -32)
                          /\ HM asegs R HIA h LB LF mm /\ aobj asegs AL CS mm X (4 * n)).

  (* [comment removed for export] *)
  Lemma tail_walk : forall (ys : list word) (mm : mem)
      (xra xt0 xt1 xt2 xs0_ xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 : word),
    DINV mm ys -> FRAME mm ->
    skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 ->
    lval ys n = (lval xs0 n * 2 ^ cnt) mod 2 ^ (32 * n) ->
    evtA asegs AL CS POST
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0_ xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xa4610) fc None mm (seg_rom asegs))
  (* [comment removed for export] *).
  Proof.
    intros until xt6. intros (HX & LX & MU & WM & MI & ST & HH & OX) FR TX VX. rt_facts.
    lxr_pose. lx_pre. lx_run_tac (PLAN [] [] 20%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    lx_post; [> exact HX | exact LX | exact TX | exact VX | .. ].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.

  Section WithZs.
    (* [comment removed for export] *)
    Variable zs : list word.
    Hypothesis LZ : length zs = length xs0.
    Hypothesis TZ : skipn (Z.to_nat n) zs = skipn (Z.to_nat n) xs0.
    Hypothesis ZZ : v0 < n -> lval zs v0 = 0.
    Hypothesis VZ : shl_vz zs xs0 n v0.

    Lemma final_value : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_shift_l ()) "Pys,(4.(2.&40.))Pr,$?.P,(26.Vv0,Vn,)P,(6.$?.(1<.R3.Vv0,)(1<.Vzs,Vv0,))P,(6.$?.(11.(3;.R4.Vv0,Vn,)(12.R3.(1>.+2.(12.+20.(29.Vn,Vv0,)))))(12.(3;.Vzs,Vv0,Vn,)(1>.+2.Vv1,)))(6.$?.(1<.R5.Vn,)(1=.(12.(1<.Vxs0,Vn,)(1>.+2.Vcnt,))(1>.+2.(12.+20.Vn,))))")
(* [comment removed for export] *).
    Proof.
      intros ys r Hv E0 INV.
      rewrite (shl_phase2_value zs ys n v0 v1 r) by first [lia | apply ZZ; lia | exact E0 | exact INV].
      unfold shl_vz in VZ. rewrite VZ. rewrite Z.mul_mod_idemp_l by (apply Z.pow_nonzero; lia).
      rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. lia.
    Qed.

  Section Phase2.
    Hypothesis Hv1 : 0 < v1 < 32.
    Hypothesis Hv0 : v0 < n.

    (* [comment removed for export] *)
    Lemma loop2_walk : forall (k : nat) (i : Z) (ys : list word) (r0w : word) (mm : mem)
        (xra xs0_ xs1 xs2 xt3 xt4 xt5 xt6 : word) (ep ei ev1 esh : Z),
      Z.to_nat (n - i) = k -> v0 <= i < n -> ep = X + 4 * i -> ei = i -> ev1 = v1 -> esh = 32 - v1 -> 0 < X ->
      DINV mm ys -> FRAME mm ->
      (forall q : nat, (Z.to_nat i <= q)%nat -> nth_error ys q = nth_error zs q) ->
      lval ys v0 = lval zs v0 ->
      shl_inv ys zs v0 i (w32 r0w) v1 -> ltp2 (w32 r0w) v1 ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp r0w (Z_to_bv 64 ep) (Z_to_bv 64 1) xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n)
                 (Z_to_bv 64 ep) (Z_to_bv 64 ev1) (Z_to_bv 64 1) SB (Z_to_bv 64 ei) (Z_to_bv 64 esh)
                 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xa45a8) fc None mm (seg_rom asegs))
    (* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i ys r0w mm xra xs0_ xs1 xs2 xt3 xt4 xt5 xt6 ep ei ev1 esh
        Hk Hi Ep Ei Ev1 Esh XP (HX & LX & MU & WM & MI & ST & HH & OX) FR FY E0 INV HR; [exfalso; clear - Hk Hi; lia|].
      subst ev1 esh. rt_facts.
      lx_limb_rw HX i Ep ltac:(clear - Hi Rv; lia) ltac:(clear - Hi Rv Ln LX L0; lia) w NX.
      lx_hide HX. lx_hide MU. lx_hide WM.
      (* [comment removed for export] *)
      lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa45dc] [(0xa45cc, DJoin)] 40%N). lx_tree.
      all: lx_unhide; lx_same_mem; lx_gc; try clear OQH.
      rewrite lx_sx32.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      lx_mkR. lx_hide HX. lx_hide MU. lx_hide WM.
      lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa45a8; 0xa4610] [] 40%N). lx_tree.
      all: lxr_leaf; lx_unhide; lx_gc.  (* [comment removed for export] *)
      all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_aobj X OX'.
      all: match goal with CX' : rw_cells asegs ?m2 ?e [C4 ?vn] |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
             pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(clear - Hi Rv; lia) Ep MUl WMl CX') as HX' end.
      all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(clear - Ep Hi Rv; lia) ltac:(clear - Ep Hi; lia)) as MU'.
      all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
      all: match goal with K : u32arr _ _ X (upd _ _ ?vn) |- _ =>
             pose proof (limb32_upd_same ys (Z.to_nat i) vn ltac:(clear - Hi Rv Ln LX L0; lia)) as VX;
             assert (LX' : length (upd ys (Z.to_nat i) vn) = length xs0) by (rewrite upd_length; exact LX) end.
      all: assert (VW : limb32 zs (Z.to_nat i) = w32 w) by (apply limb32_nth_error; rewrite <- FY by (clear; lia); exact NX).
      all: pose proof (w32_range w) as WR.
      (* [comment removed for export] *)
      all: lazymatch type of HX' with u32arr _ ?m1 _ (upd _ _ ?v) =>
        assert (INV' : shl_inv (upd ys (Z.to_nat i) v) zs v0 (i + 1)
                         (w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) ((32 - v1) mod 32))))) v1)
          by (unfold shl_inv; rewrite !lseg_snoc, lseg_upd_hi, VX, VW, shl_carry_bits by (clear - Hi Rv Hv1 Ln LX L0 LZ; lia);
              rewrite (shl_limb_bits w r0w v1 Hv1 HR);
              replace (32 * (i + 1 - v0)) with (32 * (i - v0) + 32) by (clear; lia); rewrite Z.pow_add_r by (clear - Hi; lia);
              apply shl_inv_step; [exact Hv1 | clear - WR; lia | apply Z.pow_nonneg; clear; lia | exact INV | reflexivity]) end.
      all: assert (HR' : ltp2 (w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) ((32 - v1) mod 32))))) v1)
        by (unfold ltp2; rewrite shl_carry_bits by exact Hv1; apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; clear - Hv1; lia|];
            rewrite <- Z.pow_add_r by (clear - Hv1; lia); replace (32 - v1 + v1) with 32 by (clear; lia); clear - WR; lia).
      - (* [comment removed for export] *)
        assert (BR : i + 1 < n) by klia.
        eapply (IH (i + 1));
          [ clear - Hk Hi; lia | clear - Hi BR; lia | clear - Ep; lia | clear - Ei; lia | reflexivity | reflexivity | exact XP
          | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
          | assumption
          | intros q Hq; rewrite nth_error_upd_other by (clear - Hq Hi Rv; lia); apply FY; clear - Hq; lia
          | unfold lseg in E0 |- *; rewrite lval_upd_ge by (clear - Hi Rv; lia); exact E0
          | exact INV' | exact HR' ].
      - (* [comment removed for export] *)
        assert (EI : i + 1 = n) by klia.
        eapply tail_walk;
          [ exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
          | assumption | | ].
        + rewrite skipn_upd_lt, <- TZ by (clear - Hi Rv; lia). apply same_from_skipn; [| rewrite LZ; exact LX]. intros q Hq. apply FY. clear - Hq EI; lia.
        + eapply (final_value _ _ ltac:(clear - Hi; lia)).
          * unfold lseg in E0 |- *. rewrite lval_upd_ge by (clear - Hi Rv; lia). exact E0.
          * rewrite <- EI. exact INV'.
      all: match goal with |- ?g => idtac "LOOP2-LEFT:" g end.
    Qed.
  End Phase2.

    (* [comment removed for export] *)
    Lemma phase2_walk : forall (mm : mem) (xra xt0 xt1 xt2 xs0_ xs1 xa3 xa4 xs2 xt3 xt4 xt5 xt6 : word),
      0 < X -> DINV mm zs -> FRAME mm ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt) xa3 xa4 SB
                 (Z_to_bv 64 v0) (Z_to_bv 64 0) xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa4578) fc None mm (seg_rom asegs))
    (* [comment removed for export] *).
    Proof.
      intros until xt6. intros XP (HX & LX & MU & WM & MI & ST & HH & OX) FR. rt_facts.
      assert (EV1 : cnt mod 32 = v1) by (clear - Ecnt Rv Hcnt; Z.div_mod_to_equations; lia).
      lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa45a8; 0xa4610] [] 40%N). lx_tree.
      all: lx_same_mem; lx_gc; try clear OQH.
      all: rewrite ?land_31_mod, ?EV1 in *.
      all: lazymatch goal with
           | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa45a8) _ _ _ _) =>
               assert (V1 : 0 < v1 < 32) by klia; assert (V0 : v0 < n) by klia;
               eapply (loop2_walk V1 V0 (Z.to_nat (n - v0)) v0 zs (Z_to_bv 64 0));
                 first [ exact XP | exact FR
                       | exact (conj HX (conj LZ (conj MU (conj WM (conj MI (conj ST (conj HH OX)))))))
                       | reflexivity | (intros; reflexivity)
                       | (unfold shl_inv; rewrite !lseg_empty; reflexivity)
                       | (unfold ltp2; apply Z.pow_pos_nonneg; clear - V1; lia)
                       | (clear - V0 Rv; lia) | klia
                       | match goal with |- ?g => idtac "P2-LOOP-LEFT:" g end ]
           | |- _ =>
               eapply tail_walk; [ exact (conj HX (conj LZ (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR | exact TZ | ];
               unfold shl_vz in VZ; rewrite VZ;
               first [ assert (K : v1 = 0) by klia; replace cnt with (32 * v0) by (clear - K Rv Ecnt; lia); reflexivity
                     | assert (K : n <= v0) by klia; rewrite <- !shl_all_out by (clear - K Hn Rv Ecnt Hcnt LZ L0 Ln; lia); reflexivity
                     | match goal with |- ?g => idtac "P2-RET-LEFT:" g end ]
           end.
      all: match goal with |- ?g => idtac "P2-LEFT:" g end.
    Qed.
  End WithZs.

  (* [comment removed for export] *)
  Lemma zloop_walk : forall (k : nat) (zc : Z) (y0 : list word) (mm : mem)
      (xra xs0_ xs1 xs2 xt3 xt4 xt5 xt6 : word) (ep ej : Z),
    0 < X -> (1 <= k)%nat -> Z.of_nat k <= zc <= n -> ep = X + 4 * (ej - 1) -> ej = Z.of_nat k ->
    DINV mm (firstn k y0 ++ repeat (Z_to_bv 64 0) (Z.to_nat zc - k) ++ skipn (Z.to_nat zc) y0) ->
    length y0 = length xs0 -> FRAME mm ->
    skipn (Z.to_nat n) y0 = skipn (Z.to_nat n) xs0 ->
    (v0 < n -> lval (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) y0) v0 = 0) ->
    shl_vz (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) y0) xs0 n v0 ->
    evtA asegs AL CS POST
      (MS (mkR xra SP' gp tp (Z_to_bv 64 1) (Z_to_bv 64 ej) (Z_to_bv 64 1) xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n)
               (Z_to_bv 64 cnt) (Z_to_bv 64 ep) (Z_to_bv 64 ep) SB (Z_to_bv 64 v0) (Z_to_bv 64 0)
               xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xa4528) fc None mm (seg_rom asegs))
  (* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros zc y0 mm xra xs0_ xs1 xs2 xt3 xt4 xt5 xt6 ep ej XP Hk Hz Ep Ej
      (HX & LX & MU & WM & MI & ST & HH & OX) LY FR TY ZZ VZ; [exfalso; clear - Hk; lia|].
    rt_facts.
    (* [comment removed for export] *)
    lx_limb_rw HX (ej - 1) Ep ltac:(clear - Ej; lia) ltac:(rewrite LX; clear - Ej Hz Ln L0; lia) w NX.
    lx_hide HX. lx_hide MU. lx_hide WM.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4528; 0xa4578] [(0xa4548, DJoin)] 60%N). lx_tree.
    all: lxr_leaf; lx_unhide; lx_gc.
    all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_aobj X OX'.
    all: match goal with CX' : rw_cells asegs ?m2 ?e [C4 ?vn] |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
           pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(clear - Ej; lia) Ep MUl WMl CX') as HX' end.
    all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(clear - Ep Ej XP; lia) ltac:(clear - Ep Ej Hz; lia)) as MU'.
    all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: replace (Z.to_nat (ej - 1)) with k in HX' by (clear - Ej; lia).
    all: rewrite (shl_zero_step y0 _ k (Z.to_nat zc - S k)) in HX' by (rewrite LY; clear - Hz Ln L0; lia).
    all: replace (S (Z.to_nat zc - S k)) with (Z.to_nat zc - k)%nat in HX' by (clear - Hz; lia).
    all: assert (LX' : length (firstn k y0 ++ repeat (Z_to_bv 64 0) (Z.to_nat zc - k) ++ skipn (Z.to_nat zc) y0) = length xs0)
           by (rewrite !app_length, firstn_length, repeat_length, skipn_length; clear - LY Hz Ln L0; lia).
    -
      eapply (IH zc y0);
        [ exact XP | klia | clear - Hz; lia | clear - Ep Ej; lia | clear - Ej; lia
        | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
        | exact LY | assumption | exact TY | exact ZZ | exact VZ ].
    -
      assert (K0 : k = 0%nat) by klia. subst k.
      rewrite Nat.sub_0_r in HX', LX'. cbn [firstn app] in HX', LX'.
      eapply (phase2_walk (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) y0));
        [ exact LX'
        | rewrite skipn_app, repeat_length, skipn_skipn; rewrite (skipn_all2 (repeat _ _)) by (rewrite repeat_length; clear - Hz; lia);
          replace (Z.to_nat n - Z.to_nat zc + Z.to_nat zc)%nat with (Z.to_nat n) by (clear - Hz; lia); exact TY
        | exact ZZ | exact VZ | exact XP
        | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
        | assumption ].
    all: match goal with |- ?g => idtac "ZLOOP-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma zero_walk : forall (zc : Z) (ys : list word) (mm : mem)
      (xra xt2 xs0_ xs1 xa3 xa4 xs2 xt3 xt4 xt5 xt6 : word) (ezc : Z),
    1 <= zc <= n -> ezc = zc -> 0 < X ->
    DINV mm ys -> FRAME mm ->
    skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 ->
    (v0 < n -> lval (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys) v0 = 0) ->
    shl_vz (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys) xs0 n v0 ->
    evtA asegs AL CS POST
      (MS (mkR xra SP' gp tp (Z_to_bv 64 1) (Z_to_bv 64 ezc) xt2 xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n)
               (Z_to_bv 64 cnt) xa3 xa4 SB (Z_to_bv 64 v0) (Z_to_bv 64 0) xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xa450c) fc None mm (seg_rom asegs))
  (* [comment removed for export] *).
  Proof.
    intros until ezc. intros Hzc -> XP (HX & LX & MU & WM & MI & ST & HH & OX) FR TX ZZ VZ. rt_facts.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4528] [] 40%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    (* [comment removed for export] *)
    pose proof LX as LY.
    assert (EY : firstn (Z.to_nat zc) ys ++ repeat (Z_to_bv 64 0) (Z.to_nat zc - Z.to_nat zc) ++ skipn (Z.to_nat zc) ys = ys)
      by (rewrite Nat.sub_diag; cbn [repeat app]; apply firstn_skipn).
    rewrite <- EY in HX, LX.
    eapply (zloop_walk (Z.to_nat zc) zc ys);
      [ exact XP | clear - Hzc; lia | clear - Hzc; lia | clear - Hzc; lia | clear - Hzc; lia
      | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX)))))))
      | exact LY | exact FR | exact TX | exact ZZ | exact VZ ].
    all: match goal with |- ?g => idtac "ZERO-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma loop1_walk : forall (k : nat) (i : Z) (ys : list word) (mm : mem)
      (xra xs1 xa3 xa4 xs2 : word) (ei es0 et2 et3 et5 et6 : Z),
    Z.to_nat (i - v0) = k -> v0 < i <= n -> 1 <= v0 -> 0 < X -> ei = i -> es0 = 4 * i - 4 ->
    et2 = 18446744073709551615 - X -> et3 = 2305843009213693951 -> et5 = X - 4 * v0 -> et6 = 2305843009213693951 - v0 ->
    DINV mm ys -> FRAME mm ->
    (forall q : nat, (q < Z.to_nat i)%nat -> nth_error ys q = nth_error xs0 q) ->
    (forall q : nat, (Z.to_nat i <= q < Z.to_nat n)%nat -> limb32 ys q = limb32 xs0 (q - Z.to_nat v0)) ->
    skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 ->
    evtA asegs AL CS POST
      (MS (mkR xra SP' gp tp (Z_to_bv 64 1) (Z_to_bv 64 ei) (Z_to_bv 64 et2) (Z_to_bv 64 es0) xs1
               (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt) xa3 xa4 SB (Z_to_bv 64 v0) (Z_to_bv 64 0)
               xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 et3) (Z_to_bv 64 1) (Z_to_bv 64 et5) (Z_to_bv 64 et6))
          F (Z_to_bv 64 0xa447c) fc None mm (seg_rom asegs))
  (* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ys mm xra xs1 xa3 xa4 xs2 ei es0 et2 et3 et5 et6
      Hk Hi Hv0 XP Ei Es0 Et2 Et3 Et5 Et6 (HX & LX & MU & WM & MI & ST & HH & OX) FR FY HP TX; [exfalso; clear - Hk Hi; lia|].
    subst ei es0 et2 et3 et5 et6. rt_facts.
    destruct (nth_error ys (Z.to_nat (i - 1 - v0))) as [w|] eqn:NXs; [| exfalso; apply nth_error_None in NXs; clear - NXs Hi Hv0 Ln LX L0; lia].
    pose proof (u32ro_cell_at mm X ys (i - 1 - v0) (X + 4 * (i - 1 - v0)) w (u32arr_ro _ _ _ _ HX) NXs ltac:(clear - Hi Hv0; lia) eq_refl) as CSRC.
    lx_limb_rw HX (i - 1) (eq_refl (X + 4 * (i - 1))) ltac:(clear - Hi Hv0; lia) ltac:(clear - Hi Hv0 Ln LX L0; lia) wd NX.
    lx_hide HX. lx_hide MU. lx_hide WM.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa447c; 0xa450c] [(0xa44b8, DJoin); (0xa44d0, DJoin)] 80%N). lx_tree.
    all: lxr_leaf; lx_unhide; lx_gc.  (* [comment removed for export] *)
    all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_aobj X OX'.
    all: match goal with CX : rw_cells asegs ?m2 ?e [C4 ?vn] |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
           rewrite lx_sx32 in CX; replace e with (X + 4 * (i - 1)) in CX by (clear; lia); rename CX into CX' end.
    all: lx_munch_as [(X + 4 * (i - 1), X + 4 * (i - 1) + 4)].
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(clear - Hi Hv0; lia) (eq_refl (X + 4 * (i - 1))) MUl WMl CX') as HX'.
    all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(clear - Hi Hv0; lia) ltac:(clear - Hi; lia)) as MU'.
    all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: assert (VW : limb32 xs0 (Z.to_nat (i - 1 - v0)) = w32 w) by (apply limb32_nth_error; rewrite <- FY by (clear - Hi Hv0; lia); exact NXs).
    all: assert (HP' : forall q, (Z.to_nat (i - 1) <= q < Z.to_nat n)%nat -> limb32 (upd ys (Z.to_nat (i - 1)) (sx32 w)) q = limb32 xs0 (q - Z.to_nat v0)%nat)
      by (intros q Hq; destruct (Nat.eq_dec q (Z.to_nat (i - 1))) as [->|NE];
          [ rewrite limb32_upd_same, w32_of_sx32, <- VW by (clear - Hi Hv0 Ln LX L0; lia); f_equal; clear - Hi Hv0; lia
          | rewrite limb32_upd_other by (clear - NE; lia); apply HP; clear - Hq NE; lia ]).
    all: assert (LX' : length (upd ys (Z.to_nat (i - 1)) (sx32 w)) = length xs0) by (rewrite upd_length; exact LX).
    - (* [comment removed for export] *)
      assert (BR : v0 < i - 1) by klia.
      eapply (IH (i - 1));
        [ clear - Hk Hi; lia | clear - Hi BR; lia | exact Hv0 | exact XP | clear; lia | clear; lia
        | clear; lia | clear; lia | clear; lia | clear; lia
        | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
        | assumption
        | intros q Hq; rewrite nth_error_upd_other by (clear - Hq Hi Hv0; lia); apply FY; clear - Hq Hi; lia
        | exact HP'
        | rewrite skipn_upd_lt by (clear - Hi Hv0; lia); exact TX ].
    - (* [comment removed for export] *)
      assert (EI : i - 1 = v0) by klia.
      eapply (zero_walk v0 (upd ys (Z.to_nat (i - 1)) (sx32 w)));
        [ clear - Hi Hv0; lia | clear - EI; lia | exact XP
        | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
        | assumption
        | rewrite skipn_upd_lt by (clear - Hi Hv0; lia); exact TX | | ].
      + intros _. apply lval_repeat0_app. clear - Hv0; lia.
      + unfold shl_vz. apply shl_phase1_value; [clear - Hi Hv0 Ln LX L0; rewrite ?upd_length; lia | |].
        * intros q Hq. unfold limb32. rewrite app_nth1 by (rewrite repeat_length; clear - Hq; lia). rewrite nth_repeat. reflexivity.
        * intros q Hq. unfold limb32 at 1. rewrite app_nth2 by (rewrite repeat_length; clear - Hq; lia). rewrite repeat_length, nth_skipn.
          replace (Z.to_nat v0 + (q - Z.to_nat v0))%nat with q by (clear - Hq; lia). change (limb32 (upd ys (Z.to_nat (i - 1)) (sx32 w)) q = limb32 xs0 (q - Z.to_nat v0)).
          apply HP'. clear - Hq EI; lia.
    all: match goal with |- ?g => idtac "LOOP1-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma phase1_walk : forall (mm : mem) (xt0 xt1 xt2 xa3 xa4 xt3 xt4 xt5 xt6 : word),
    DINV mm xs0 -> FRAME mm ->
    evtA asegs AL CS POST
      (MS (mkR ra SP' gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt) xa3 xa4 SB
               (Z_to_bv 64 v0) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xa4440) fc None mm (seg_rom asegs))
  (* [comment removed for export] *).
  Proof.
    intros until xt6. intros (HX & LX & MU & WM & MI & ST & HH & OX) FR. rt_facts.
    destruct (Z.eq_dec n 0) as [N0|NN0].
    { lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4610] [] 80%N). lx_tree.
      all: lx_same_mem; lx_gc; try clear OQH.
      all: eapply tail_walk; [ exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR | reflexivity | ].
      all: rewrite N0, Z.mul_0_r, Z.pow_0_r, Z.mod_1_r; apply lval_nonpos; clear; lia. }
    assert (XP : 0 < X) by (clear - NZX NN0; destruct NZX; lia).
    assert (XLT : X < 2 ^ 64) by (clear - XB Hn Ln NN0; lia).
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4578; 0xa450c; 0xa447c] [] 40%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    all: lazymatch goal with
         | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa4578) _ _ _ _) =>
             (* [comment removed for export] *)
             assert (V00 : v0 = 0) by klia;
             eapply (phase2_walk xs0 eq_refl eq_refl);
               [ intros _; apply lval_nonpos; clear - V00 Rv; lia
               | unfold shl_vz; replace (32 * v0) with 0 by (clear - V00 Rv; lia); rewrite Z.pow_0_r, Z.mul_1_r; symmetry; apply Z.mod_small; apply lval_range; clear - Hn; lia
               | exact XP
               | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR ]
         | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa450c) _ _ _ _) =>
             (* [comment removed for export] *)
             assert (VN : n <= v0) by klia;
             eapply (zero_walk n xs0);
               [ clear - Hn NN0; lia | reflexivity | exact XP
               | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR | reflexivity
               | let Hv := fresh in intros Hv; exfalso; clear - VN Hv; lia
               | unfold shl_vz; rewrite lval_repeat0_app by (clear - Hn; lia); apply shl_all_out; clear - VN Hn Rv Ln L0; lia ]
         | |- _ =>
             (* [comment removed for export] *)
             eapply (loop1_walk (Z.to_nat (n - v0)) n xs0);
               first [ reflexivity | exact XP
                     | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR
                     | (intros; reflexivity) | (intros; exfalso; klia) | (clear; lia) | klia
                     | match goal with |- ?g => idtac "P1-COPY-LEFT:" g end ]
         end.
    all: match goal with |- ?g => idtac "P1-LEFT:" g end.
  Qed.
End Walk.

Lemma A_mpi_core_shift_l_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_shift_l ()) "PR,$47.PHIA,(48.$37.R1.)P,(49.(32.R2.))P,(6.$?.(4:.R3.)$4;.)P,(24.=(2;.R4.))(4<.$37.R5.R4.$4=.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS NEED0. unfold mpi_core_shift_l_stmtA, A_MPI_CORE_SHIFT_L.
  intros until xs. intros HH HX Hn LX Hcnt ALX NZX XLT ST LOS LO TOP SPA SX CWX MI RA OX -> -> ->.
  unfold MPI_CORE_SHIFT_L_STACK_A in *.
  pose (lxi := lxA_img (arl_AL R) IMG).
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
  pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
  pose proof (u32arr_bound _ _ _ _ HX) as XB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by klia.
  assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| klia| klia]).
  pose proof (munch_refl [(X, X + 4 * n); (lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (Z.div_mod cnt 32 ltac:(klia)) as DM. pose proof (Z.mod_pos_bound cnt 32 ltac:(klia)) as MB.
  pose proof (Z.div_pos cnt 32 ltac:(klia) ltac:(klia)) as DP.
  pose proof (hm_abase asegs R HIA h LB LF m HH) as ABS.
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4440] [] 40%N). lx_tree.
  all: lxr_leaf; lx_carry; lx_gc.
  clear HX ABS. lx_rn_u32 X HX. lx_rn_munch MU. lx_rn_wmono WM.
  assert (E5 : cnt ≫ 5 = cnt / 32) by (rewrite Z.shiftr_div_pow2 by (clear; klia); reflexivity). rewrite ?E5 in *.
  eapply phase1_walk with (v0 := cnt / 32) (v1 := cnt mod 32) (lx := Z.of_nat (length xs)).
  all: lazymatch goal with
       | |- _ /\ _ => repeat (lazymatch goal with |- _ /\ _ => split end); first [exact HX | reflexivity | eassumption | klia]
       | |- _ => idtac end.
  all: first [eassumption | reflexivity | klia | idtac].
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.

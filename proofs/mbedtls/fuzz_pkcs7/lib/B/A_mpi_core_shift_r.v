(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_shift_r.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P016132201808f5a4 0 5 0 1 44 1 50 1 57 1 58 1P0167d4a9e807798d 0 2 0 1 10 1P02491cddd848035e 1 1 16 6 0 4 31 16 46 4 50 4 71 4 72 4 2 51 1 73 1P0308b234fdd965b0 0 2 0 1 4 1P0364a207a4b737e8 1 1 16 6 0 4 29 16 44 4 48 4 67 4 68 4 2 49 1 69 1P041d7c1a2219e3d3 0 2 0 1 2 1P0482c27bbc306912 1 1 16 5 0 4 31 16 50 4 72 4 73 4 2 52 1 74 1P04c81016a84e4f27 1 1 16 6 0 4 29 16 44 4 48 4 67 4 68 4 2 49 1 69 1P056f4b99bc090603 0 5 0 1 21 1 31 1 47 1 51 1P05719e9b1b14833b 0 2 0 1 1 1P05849e589620add6 0 2 0 1 23 1P05d9f34a47cc9504 0 7 0 4 29 16 51 4 53 16 54 16 76 4 77 4P0664c9adaab9c17d 0 3 0 1 18 1 28 1P06b3588d874d2a62 0 6 0 16 28 64 43 16 47 16 67 16 68 16P07bd39c5b584c23d 0 5 0 1 44 1 50 1 57 1 58 1P084bf697a49978cc 0 2 0 1 23 1P087051dd9cf4d022 0 5 0 1 46 1 53 1 62 1 63 1P091ce024ea153daf 0 2 0 1 59 1P094fc020baad501f 0 2 0 1 2 1P09d3017b2c2629ff 0 2 0 1 5 1P0a46469e3b2b4459 0 6 0 1 44 1 45 1 50 1 57 1 58 1P0aa8e2c7bee71348 0 2 0 1 24 1P0b6b5587ab09044f 0 2 0 1 25 1P0b968e3e99f5bec0 0 7 0 4 31 16 53 4 55 16 56 16 80 4 81 4P0bbfe1921955199d 0 7 0 4 30 16 52 4 53 16 54 16 76 4 77 4P0bd28d15549abfe5 0 2 0 1 2 1P0c2772d958ad3e42 0 2 0 1 1 1P0c444a8bc0f84acb 0 6 0 1 44 1 45 1 50 1 57 1 58 1P0c4f65b3b25eb750 0 5 0 4 32 16 51 4 72 4 73 4P0cb1030d480a39eb 0 2 0 1 60 1P0d3f4c766b6e74d1 0 5 0 1 45 1 52 1 57 1 58 1P0db2e1ebf4ca854a 0 5 0 4 31 16 50 4 71 4 72 4P0ed4c68189b02a3b 0 2 0 1 2 1P0f1b8b0472a3d56b 0 2 0 1 1 1P0f5d620a17172299 0 2 0 1 8 1P0fd07ca1520d16d1 0 3 0 1 24 1 46 1P1005fbd3ca04ec7a 0 3 0 1 47 1 52 4P1008e4db5bfaa1b0 2 45 1 1 4 3 3 1 61 1 62 1 6 0 1 47 1 53 1 60 1 63 1 64 4 1 1 4 3 2 1 60 1 63 1 4 0 4 61 4 62 4 64 16P1031ca875558a702 0 2 0 1 80 1P109830da0e0f2dff 0 5 0 1 45 1 52 1 57 1 58 1P10ef3d34ee42ad28 0 2 0 1 28 1P11a1499a1b63e1e6 0 5 0 1 44 1 50 1 57 1 58 1P1268e85d0827690d 0 5 0 1 44 1 50 1 57 1 58 1P12fb02806dd38c63 0 2 0 1 18 1P1387b52f24c1e0cf 2 45 1 1 4 3 3 1 61 1 62 1 6 0 1 47 1 53 1 60 1 63 1 64 4 1 1 4 3 2 1 60 1 63 1 4 0 4 61 4 62 4 64 16P13b15a56e08e904f 0 5 0 1 46 1 53 1 62 1 63 1P15a4a574e842c34b 2 45 1 1 4 3 3 1 61 1 62 1 6 0 1 47 1 53 1 60 1 63 1 64 4 1 1 4 3 2 1 60 1 63 1 4 0 4 61 4 62 4 64 16P15ac56b60862d398 0 2 0 1 1 1P15ac6f66e21964bf 0 5 0 1 46 1 53 1 62 1 63 1P15b58263cab59e69 0 5 0 1 45 1 52 1 57 1 58 1P15d87913da638acd 0 5 0 1 46 1 53 1 62 1 63 1P15d8b5acc9835cbd 2 45 1 1 4 3 3 1 61 1 62 1 6 0 1 47 1 53 1 60 1 63 1 64 4 1 1 4 3 2 1 60 1 63 1 4 0 4 61 4 62 4 64 16P162d8c2673b0879b 0 2 0 1 1 1P16c4372de99ecfde 0 3 0 1 24 1 46 1P1744f055d6db88de 0 7 0 4 23 16 43 4 45 16 46 16 72 4 73 4P178f17310b8ffd50 0 5 0 1 45 1 52 1 57 1 58 1P17c8778d9307112f 0 2 0 1 19 1P186fa234b5ce8343 0 5 0 1 44 1 50 1 57 1 58 1P199b516783aadd5c 0 5 0 1 44 1 50 1 57 1 58 1P1a38b0239f14a29d 0 2 0 1 59 1P1b1a35803a962007 0 2 0 1 2 1P1b4c132d33295587 0 2 0 1 2 1P1cc6f4f331bb0424 0 3 0 32 23 1 58 1P1d1861ade2bdd6da 0 3 0 1 1 1 21 1P1d3e7824f35bb795 0 2 0 1 21 1P1d3f00f343665516 0 2 0 1 22 1P1e0914376b3eec67 0 2 0 1 71 1P1e3841d28dda262a 0 2 0 1 22 1P1ffa600fefebcfad 1 1 16 5 0 4 30 16 49 4 71 4 72 4 2 51 1 73 1P2168a15ec5247758 0 3 0 1 24 1 46 1P223eefe863258961 0 4 0 1 43 1 57 1 58 1P22b2fff3f84537c0 0 2 0 1 60 1P22fb9e74b299a2f3 0 2 0 1 1 1P237da0391026df70 0 2 0 1 2 1P23a1560190f97444 1 1 16 6 0 4 32 16 47 4 51 4 70 4 71 4 2 52 1 72 1P23dd3d24f35d757d 0 5 0 1 44 1 50 1 57 1 58 1P23f3a388c86f8fb5 0 2 0 1 25 1P23fbb57e62702316 0 6 0 1 44 1 45 1 50 1 57 1 58 1P242dbe2af34318dc 0 2 0 1 1 1P24552a3b4818bc81 0 2 0 1 22 1P24b800cdd9fa9104 0 2 0 1 1 1P24d7b8175cebc40e 2 45 1 1 4 3 3 1 61 1 62 1 6 0 1 47 1 53 1 60 1 63 1 64 4 1 1 4 3 2 1 60 1 63 1 4 0 4 61 4 62 4 64 16P26201a2d708e2267 0 2 0 1 8 1P2692ce19cd326e5d 0 2 0 1 30 1P26f0698b12dfa21f 0 2 0 1 43 1P2770c8fec078b8de 0 2 0 1 21 1P279f8a8a3a1f888d 0 2 0 1 28 1P280dc49c464751af 0 3 0 32 22 1 57 1P2875d4f132d2f499 0 2 0 1 8 1P28c9e0ebe97ca467 0 2 0 1 21 1P2922d81b6545b7b6 0 7 0 4 32 16 54 4 56 16 57 16 79 4 80 4P293b641151b145ad 0 3 0 32 24 1 59 1P29418e31d79e2766 0 2 0 1 27 1P294bc412afc3a590 0 4 0 1 43 1 57 1 58 1P297957d195cce721 2 51 0 11 0 1 1 1 25 4 45 1 47 4 48 4 52 1 58 4 59 1 74 1 75 1 0 8 0 1 2 1 26 4 46 1 47 4 48 4 74 1 75 1P2a4583a2a6ff8108 0 3 0 1 1 1 21 1P2a5039a404e8c16b 0 2 0 1 71 1P2b67410472bbc033 0 7 0 4 30 16 52 4 53 16 54 16 76 4 77 4P2bacdb92d888d61a 0 4 0 1 12 1 23 1 45 1P2c0a2001ecb2f17f 0 6 0 1 44 1 45 1 50 1 57 1 58 1P2c6b020a2385f2af 0 7 0 4 32 16 54 4 55 16 56 16 80 4 81 4P2cf44b3125eab883 0 6 0 16 28 64 43 16 47 16 67 16 68 16P2daacf81cfc01cd2 0 2 0 1 22 1P2e1c0b740f9a21fd 0 6 0 4 30 16 49 4 51 16 71 4 72 4P2e31004a581b248e 0 2 0 1 20 1P2e366cb93df42db2 0 2 0 1 27 1P2e6971d7af08b898 0 2 0 1 20 1P2f4d9dc5634f5c8e 0 5 0 1 46 1 53 1 62 1 63 1P2f892f1a134d2e47 0 2 0 1 1 1P2f9355cab202e049 0 4 0 1 43 1 57 1 58 1P2faa0dcd203f1e78 0 4 0 1 43 1 57 1 58 1P30169c90a54d7037 0 2 0 1 2 1P310002f5e6183553 0 5 0 1 21 1 31 1 47 1 51 1P310817616bd3c568 0 6 0 4 30 16 49 4 51 16 71 4 72 4P317c922e8c92ea34 0 4 0 1 43 1 57 1 58 1P31b41cdb5f24d388 0 2 0 1 19 1P31e43d10f8fd5eaf 0 2 0 1 80 1P325fe55fbbfc7f3d 0 2 0 1 1 1P32aa34ed3b1655b5 2 55 1 1 4 9 0 1 1 1 32 4 51 1 55 1 61 4 62 1 73 1 74 1 2 53 1 75 1 0 6 0 16 2 16 33 64 52 16 73 16 74 16P33490d10e00768e0 0 3 0 1 19 1 43 1P3411c4156ca8187e 0 5 0 1 44 1 50 1 57 1 58 1P341fd85280140c5d 0 2 0 1 19 1P342fab1ef5cfe550 0 2 0 1 28 1P351e4eafafef05e2 0 2 0 1 28 1P357732947f2bfcb4 0 2 0 1 59 1P35e2cf883486285b 0 6 0 16 30 64 45 16 49 16 71 16 72 16P35f9c978a42bbcd7 0 2 0 1 9 1P35fc8aa4f511ffa9 0 2 0 1 27 1P365940e6a6aec275 0 3 0 1 30 1 48 1P3686abf297e4d52d 0 2 0 1 20 1P36da0a2d3564bf8a 0 6 0 16 31 64 46 16 50 16 70 16 71 16P37257891528608b0 0 2 0 1 5 1P373cbfd415d3d419 0 7 0 4 33 16 55 4 56 16 57 16 79 4 80 4P37e259ffc576f0b8 0 4 0 1 12 1 23 1 45 1P37f6fff53d685a08 0 3 0 1 19 1 43 1P382295fee8b6c75c 0 5 0 4 31 16 50 4 71 4 72 4P38254f91d6de46d3 0 7 0 4 24 16 44 4 45 16 46 16 72 4 73 4P387f363d427caed3 0 2 0 1 2 1P395397558468ec48 0 5 0 1 45 1 52 1 57 1 58 1P3957cbaf6aea599a 0 5 0 1 44 1 50 1 57 1 58 1P3a347be4b10096a4 0 5 0 1 44 1 50 1 57 1 58 1P3b8823446526e504 0 6 0 1 44 1 45 1 50 1 57 1 58 1P3c02056b63fb50bc 0 5 0 4 31 16 50 4 71 4 72 4P3c39abdc2afb608b 0 3 0 32 24 1 59 1P3c42175ff7d11b3b 0 3 0 1 30 1 48 1P3c79429b08126772 0 2 0 1 20 1P3cb3ef4fe65a33fa 0 7 0 4 29 16 51 4 53 16 54 16 76 4 77 4P3d1ad46a4ce1ec1b 0 3 0 1 30 1 48 1P3d42a45c1bc4cbd5 0 2 0 1 19 1P3dca0cb132479170 0 2 0 1 20 1P3f0fe5ee47b8e1a3 0 5 0 1 45 1 52 1 57 1 58 1P3f6fee6c9739f747 0 5 0 1 46 1 53 1 62 1 63 1P3f958513f76ad9e2 0 2 0 1 4 1P3f9cd8fc47287624 0 2 0 1 29 1N012c8d71ece1b995N014d7e62f2f9cb0cN01c73ad3c9bac698N01fe292182624302N02cd51389d49408bN03e8f085d7e44d4dN05db9f999fc24297N06002d5fcce08856N061eca6f79a6f155N06a45889248e1dc9N06bbccebef409301N06e4cd665ea8922eN079161f6cfa0e91dN0858274ebc5f2dddN0872c1e0eb372650N08f5061e8c1393e0N0a4b3971673a2cfeN0a6c33e85141f1d8N0b399a981ac16faaN0b570ffe64dc5d52N0b7989a7e17def15N0bb8d5b77ea61d38N0ce3a6866902ecfaN0cfec9d28071b4c6N0d6ddbc0a81572bdN0d90f43359665078N0fa29ed99adf70a8N0fb9bd0342c624b4N108b94b3c73b8a2dN1097bc46cd62f4e2N10a5606fcfec13deN110cad816db23137N12056afc6dc01268N12edcbe3404d5c16N14de127b76bc5f5dN15c9da604d360ff3N179c92e2550e27b4N17b9987c87cddff8N191ddb2b6fb62913N1970b8d8b429c041N1999bded66ab4a73N19a87c3bdc36e8f6N19cedeab77344ca3N1b15e3dcc39448ccN1b7968b9d1843ec7N1cea129d8c358edbN1cefe02ab5410a3aN1d5056b972f0ec8cN1d525087963cb1b1N1d55a0ed33b605e8N1d676516381c232eN1d800f3a14ef4ebdN1d831a9ad98be38eN1ede9a3c15564d38N1ef533bb15d789c4N1fc351bbacd26632N204bfb12fcb97673N20bf8b1fd610a855N22156ad6584b6534N2279e0aa8f2c4dd0N22e76b61d22a5176N23b15c9471c7ede3N23fb3436f200c482N251ed02f4c7541aeN25971715a2d59799N25b88fa1631950b2N25da75ed54e6c523N2635de6819860309N26495e2fda7bdc5fN26579961a9cc4020N26f955213a4fa164N28930565843e0e2fN2aa6b4ad094bca67N2cf6abdb0fd00db0N2dfcc7ba3a5dfe64N2e270ffcadd00d95N2fb4a04e77a66df1N3054ab14c9c3c505N3078603d22c75042N30a4e7a9adf88c88N30c0d2eb49d51c87N319b139464c64f92N31be929eb627761aN31d897bf93c3fa03N32b414861525a837N32bdec6447d98729N336c0ca62d77ef72N337b5646a7511536N34683ef5e06c3e91N3490f1bec8a1750aN35cc76799a17ca05N35e5cc9abdc3482aN36e96bf27ede74f1N37c6cc1fb99b6600N3989fbfd70ff939aN39b66aad627ac610N39dae9e2810539e8N3aa5e877f4e8df09N3aab19ce3e4d5eccN3ae7a8e148acdd80N3b2f36c4a9b0363dN3ba23af5d190b410N3cdae963ff72559dN3d43229e14d7fb18N3d4df0b853cf1935N3da7703fa5d8c81cN3df2a176ea489ea0N3e6a23b87362c9e5N3e7b9b2bee8e6290N3f2fd7528229accaN3f46dfd633896a87N3fb0c9ea23d6d3c7N3fd66bb9d9e5148b"%lxh.
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
Ltac2 gd_tbl_A_mpi_core_shift_r () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_SHIFT_R_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_shift_r_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Peano.lt"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lseg"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.w32"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "A_ASAN_MEMSET_SR"; "mpi_core_shift_r_stmtA"; "A_MPI_CORE_SHIFT_R"].


Definition A_MPI_CORE_SHIFT_R : Z := 0xa41bc.   (* [comment removed for export] *)
Definition A_ASAN_MEMSET_SR : Z := 0x68258.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition MPI_CORE_SHIFT_R_STACK_A : Z := 48.

Definition mpi_core_shift_r_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n cnt : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_shift_r ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(9.O18.)O7.(:.(2.&40.))R2.(;.O1>.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O6.(11.O6.(12.+4.O5.)))(=.(>.$?.$?.)(10.$?.$?.O2.(13.&40.O17.))(14.(>.$?.$?.))))O1.R2.)(5.(15.O1>.O1.R2.)(5.(16.O1>.R2.)(5.(17.O1>.R2.O6.R1.)(5.(6.$18.(19.(2.&40.)R1.)(19.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1:.(2.&40.)(1;.O5.)R1.)(1:.(2.&40.)(1;.O5.)O3.))(5.(6.$?.(1<.R1.O5.)(1=.(1<.O3.O5.)(1>.+2.O4.)))(5.(1?.O1>.R2.O2.(13.&40.O17.))(20.O1>.O1=.O1<.O1;.O1:.O19.R2.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_shift_r_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_shift_r ()) "Ph,(21.O4.O3.O2.)PLB,(4.$22.)PLF,(4.$22.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.Pn,$?.Pcnt,$?.Plo,$?.Pxs,(4.(2.&40.))P,(20.O4.O3.O2.R2:.R29.R28.R6.)P,(17.O4.R7.R6.R2.)P,(5.(24.+1.R6.)(24.R6.+2710.))P,(24.R7.(25.(19.(2.&40.)R4.)))P,(5.(24.=R7.)(26.R7.(1>.+2.+40.)))P,(6.$?.(27.R:.+4.)=)P,(26.=R;.)P,(1?.O4.R=.R9.(13.&40.R2=.))P,(24.(28.O3.)R:.)P,(24.R;.(29.(29.(13.&40.R2?.)$2:.)(2;.O3.)))P,(24.(13.&40.R30.)(2<.O4.O3.O2.R34.))P,(6.$?.(27.(13.&40.R31.)+10.)=)P,(2=.(24.(11.R11.(12.+4.(25.(19.(2.&40.)R=.))))R>.)(24.(13.&40.R32.)R11.))P,(2>.(2?.O3.)(30.$22.R36.(31.R35.))(28.O3.)(2<.O4.O3.O2.R37.)R12.(12.+4.R11.))P,(16.O4.R14.)P,(6.$?.(27.(13.&40.R36.)+2.)=)P,(32.O4.(33.O3.)(34.O4.O3.O2.R3:.)R16.R15.(12.+4.R14.))P,(6.(2.&40.)R2?.(35.&40.R16.))P,(6.(2.&40.)R2?.(35.&40.R16.))P,(6.(2.&40.)R2?.(35.&40.R16.))(36.O4.(33.O3.)(34.O4.O3.O2.R3>.)(37.O4.O3.O2.R3>.R3=.R3<.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.R19.R18.R17.R15.R16.R1:.)(7.(8.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R1<.(35.&40.O1.)R1;.(:.(2.&40.))R1:.(;.O4.)))")
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

Lemma shr_upd_mid : forall (P tl : list word) (y x : word), upd (P ++ y :: tl) (length P) x = P ++ x :: tl.
Proof. induction P as [|a P IH]; intros tl y x; cbn [app length upd]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma shr_zero_step : forall (A ys : list word) (r j : nat), j = (length A + r)%nat -> (j < length ys)%nat ->
  upd (A ++ repeat (Z_to_bv 64 0) r ++ skipn j ys) j (Z_to_bv 64 0)
  = A ++ repeat (Z_to_bv 64 0) (S r) ++ skipn (S j) ys.
Proof.
  intros A ys r j -> Hj.
  assert (E : forall k (l : list word), (k < length l)%nat -> skipn k l = nth k l (Z_to_bv 64 0) :: skipn (S k) l).
  { induction k as [|k IH]; intros [|y l] Hk; cbn [length skipn nth] in Hk |- *; try lia; [reflexivity|]. apply IH. lia. }
  rewrite (E _ ys Hj), app_assoc.
  assert (LP : length (A ++ repeat (Z_to_bv 64 0) r) = (length A + r)%nat) by (rewrite length_app, repeat_length; reflexivity).
  pose proof (shr_upd_mid (A ++ repeat (Z_to_bv 64 0) r) (skipn (S (length A + r)) ys) (nth (length A + r) ys (Z_to_bv 64 0)) (Z_to_bv 64 0)) as U.
  rewrite LP in U. rewrite U, <- app_assoc. f_equal.
  generalize (skipn (S (length A + r)) ys) as tl. clear. intro tl.
  induction r as [|r IH]; cbn [repeat app]; [reflexivity | cbn [repeat app] in IH; rewrite IH; reflexivity].
Qed.


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_SR.
  Hypothesis NEED0 : 0 <= arl_need_amem R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0 s1 s2 s3 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n cnt v0 v1 lx lo : Z) (xs0 : list word) (junk : list byte).
  Hypothesis Hn : 1 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
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

  Notation POST := (mpi_core_shift_r_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cnt xs0 lo m).
  Notation W := [(X, X + 4 * n); (lo, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation DINV mm ys := (u32arr asegs mm X ys /\ length ys = length xs0
                          /\ munch W m mm /\ wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -32)
                          /\ HM asegs R HIA h LB LF mm /\ aobj asegs AL CS mm X (4 * n)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?D16567456097.95D5483095183.95 D563007111.96  D62022258533.96L29428324939.5 L35653441506.7 L60098763854.3 00000I00b01C01^02002H02RS2ra2sp1X1n3cnt3xs02ys2LXS2ra2sp1X1n3cnt3xs02ys2LXS1R3HIA1h2ra2sp1X1n3cnt3xs02ys2LXS1R2ra2sp1X1n3cnt3xs02ys2LXS1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1R2lo3LOS". (* [comment removed for export] *)
  Lemma tail_walk : forall (ys : list word) (mm : mem)
      (xra xt0 xt1 xt2 xs0_ xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      DINV mm ys -> FRAME mm ->
      skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 ->
      lval ys n = lval xs0 n / 2 ^ cnt ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0_ xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa41f8) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros (HX & LX & MU & WM & MI & ST & HH & OX) FR TX VX. rt_facts.
    lxr_pose. lx_pre. lx_run_tac (PLAN [] [] 20%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    lx_post; [> exact HX | exact LX | exact TX | exact VX | .. ].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section WithZs.
    (* [comment removed for export] *)
    Variable zs : list word.
    Hypothesis LZ : length zs = length xs0.
    Hypothesis TZ : skipn (Z.to_nat n) zs = skipn (Z.to_nat n) xs0.
    Hypothesis VZ : lval zs n / 2^v1 = lval xs0 n / 2^cnt.

  Section Phase2.
    Hypothesis Hv1 : 0 < v1 < 32.

    Local Ltac2 Set LiaOrc.tbl := fun () => "00U0@D16567013645.113D5483439331.113 D563007111.114  D62022258533.114L15366984773.6  L16034111730.0  L17297183226.3  L17318389497.3  L18312272203.4  L19592319389.2  L21007906567.2  L27859920703.6  L29428324939.5  L32193184416.9  L34328786283.5  L35653441506.7  L37442977898.2  L40568343070.3  L41250020593.3  L41418080589.2  L43934131628.4  L4988623391.6   L53380753436.5  L53768766698.9  L59308551419.4  L59308586248.4  L59796884125.1  L60098763854.3  L60712590571.0  L60720403804.2  L62070454720.116L62891341106.6  L66351018677.2  L66806775440.5  L67984097661.1  L7572164765.3   L8632193901.1   00000[01F02902f03803903A03J03U03\03b04204D04_04l05D05L05T05\05]05h06906A06S06`06k06n07807907?08008@08F08S08V08^08aS2ra2sp1X1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LXS2ra2sp1X1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LXS1R3HIA1h2ra2sp1X1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LXS1R2ra2sp1X1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LXS1n1i2ei2Hi2Ei3H10SS1n1i2HiS1i2ei2EiS1X1i2ep2EpS1i3Ei1S1n2HnS1X1n1i2ep2Hi2EpS1R2lo3LOS3ALO3ACPS1n2lx3xs02Ln2L01i2ys2Hi2LXS1n1i2Hi1q2HqS1R3HIA1h2sp2lo3TOP4HTOPS2v13Hv1S1n1i2HiS1n1i2HiSS1n2zs1i2LRS1n1i2ei2Hi2Ei2BRS1i1q2HqS1n3xs02zs2LZ1i2HiS1i2ys3IBw2NXS1n1i2Hk2HiS1nS1R2lo3LOSSS1w2WRS2ra2sp1X1n3cnt2v02v13xs02Rv2zs2LZ1k1i2ys1C2Hk2LXS1X1n1i2ep2Hi2EpS1C2CBS1n1k1i2Hk2HiS1iS1n1i2HiS1i". (* [comment removed for export] *)
    Lemma loop2_walk : forall (k : nat) (i : Z) (ys : list word) (r0w : word) (C Rr : Z) (mm : mem)
        (xra xs0_ xs1 xt3 xt4 xt5 xt6 : word) (ep esh ea3 et2 : Z),
      Z.to_nat i = k -> 1 <= i <= n -> ep = X + 4 * (i - 1) -> esh = 32 - v1 -> ea3 = - i ->
      et2 = i + 2305843009213693951 ->
      DINV mm ys -> FRAME mm ->
      (forall q : nat, (q < Z.to_nat i)%nat -> nth_error ys q = nth_error zs q) ->
      skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 ->
      lseg ys i n = lseg zs i n / 2 ^ v1 ->
      lseg zs i n = C + 2 ^ 32 * Rr -> 0 <= C < 2 ^ 32 -> 0 <= Rr ->
      w32 r0w = C mod 2 ^ v1 * 2 ^ (32 - v1) ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp (Z_to_bv 64 1) (Z_to_bv 64 ep) (Z_to_bv 64 et2) xs0_ xs1 (Z_to_bv 64 X)
                 (Z_to_bv 64 ep) (Z_to_bv 64 1) (Z_to_bv 64 ea3) SB (Z_to_bv 64 v1) r0w (Z_to_bv 64 esh)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa42e4) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i ys r0w C Rr mm xra xs0_ xs1 xt3 xt4 xt5 xt6 ep esh ea3 et2
        Hk Hi Ep Esh Ea3 Et2 (HX & LX & MU & WM & MI & ST & HH & OX) FR FY TY INV HC CB RB HR; [exfalso; clear - Hk Hi; lia|].
      subst esh ea3 et2. rt_facts.
      lx_limb_rw HX (i - 1) Ep ltac:(clear - Hi; lia) ltac:(clear - Hi Ln LX L0; lia) w NX.
      lx_hide HX. lx_hide MU. lx_hide WM.
      (* [comment removed for export] *)
      lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4320] [(0xa4308, DJoin)] 40%N). lx_tree.
      all: lx_unhide; lx_same_mem; lx_gc; try clear OQH.
      rewrite lx_sx32.
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      lx_mkR. lx_hide HX. lx_hide MU. lx_hide WM.
      lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa42e4; 0xa41f8] [] 40%N). lx_tree.
      all: lxr_leaf; lx_unhide; lx_gc.  (* [comment removed for export] *)
      all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_aobj X OX'.
      all: match goal with CX' : rw_cells asegs ?m2 ?e [C4 ?vn] |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
             pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(clear - Hi; lia) Ep MUl WMl CX') as HX' end.
      all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(clear - Ep Hi; lia) ltac:(clear - Ep Hi; lia)) as MU'.
      all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
      all: match goal with K : u32arr _ _ X (upd _ _ ?vn) |- _ =>
             pose proof (limb32_upd_same ys (Z.to_nat (i - 1)) vn ltac:(clear - Hi Ln LX L0; lia)) as VX;
             assert (LX' : length (upd ys (Z.to_nat (i - 1)) vn) = length xs0) by (rewrite upd_length; exact LX) end.
      all: rewrite (lx_shr_limb_bits w r0w v1 (C mod 2 ^ v1) Hv1 ltac:(apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; clear - Hv1; lia) HR) in VX.
      (* [comment removed for export] *)
      all: assert (VW : limb32 zs (Z.to_nat (i - 1)) = w32 w) by (apply limb32_nth_error; rewrite <- FY by (clear - Hi; lia); exact NX).
      all: pose proof (w32_range w) as WR.
      - (* [comment removed for export] *)
        match goal with K : _ |- _ => assert (BR : 2 <= i) by (clear - K Hi; lia) end.
        eapply (IH (i - 1) _ _ (w32 w) (lseg zs i n));
          [ clear - Hk Hi; lia | clear - Hi BR; lia | clear - Ep; lia | first [reflexivity | clear; lia] | clear; lia | clear; lia
          | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
          | assumption
          | intros q Hq; rewrite nth_error_upd_other by (clear - Hq Hi; lia); apply FY; clear - Hq Hi; lia
          | rewrite skipn_upd_lt by (clear - Hi; lia); exact TY
          | | rewrite (lseg_cons zs (i - 1) n), VW by (clear - Hi; lia); f_equal; f_equal; f_equal; clear; lia
          | clear - WR; lia | pose proof (lseg_range zs i n ltac:(clear - Hi Ln LZ L0; lia)) as LR; clear - LR; lia
          | apply shr_carry_bits; exact Hv1 ].
        rewrite (lseg_cons (upd ys (Z.to_nat (i - 1)) _) (i - 1) n) by (clear - Hi; lia). rewrite VX.
        replace (i - 1 + 1) with i by (clear; lia).
        replace (lseg (upd ys (Z.to_nat (i - 1)) _) i n) with (lseg ys i n)
          by (unfold lseg; rewrite skipn_upd_lt by (clear - Hi; lia); reflexivity).
        rewrite (lseg_cons zs (i - 1) n), VW by (clear - Hi; lia). replace (i - 1 + 1) with i by (clear; lia).
        eapply shr_step_arith; [exact Hv1 | exact WR | clear - CB; lia | exact RB | exact HC | exact INV].
      - (* [comment removed for export] *)
        eapply tail_walk;
          [ exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
          | assumption
          | rewrite skipn_upd_lt by (clear - Hi; lia); exact TY | ].
        match goal with K1 : _ |- _ => assert (Ei1 : i = 1) by (clear - K1 Hi; lia) end.
        rewrite <- VZ.
        assert (E0 : forall ws, lval ws n = lseg ws 0 n) by (intros; unfold lseg; cbn [Z.to_nat skipn]; f_equal; clear; lia).
        rewrite !E0. rewrite (lseg_cons (upd ys _ _) 0 n), (lseg_cons zs 0 n) by (clear - Hn; lia).
        replace (Z.to_nat (i - 1)) with (Z.to_nat 0) in VX |- * by (clear - Ei1; lia). rewrite VX.
        rewrite Ei1 in VW, INV, HC. replace (1 - 1) with 0 in VW by (clear; lia). rewrite VW. change (0 + 1) with 1.
        replace (lseg (upd ys (Z.to_nat 0) _) 1 n) with (lseg ys 1 n) by (unfold lseg; rewrite skipn_upd_lt by (clear; lia); reflexivity).
        eapply shr_step_arith; [exact Hv1 | exact WR | clear - CB; lia | exact RB | exact HC | exact INV].
      all: match goal with |- ?g => idtac "LOOP2-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Phase2.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?D16567456097.93D5483095183.93 D563007111.94  D62022258533.94L18174687275.0 L220361425.3   L29428324939.5 L30532176484.3 L35653441506.7 L37442977898.2 L39280637297.0 L39543213015.2 L44822659963.2 L50959335723.1 L54397133940.3 L56104965185.0 L60098763854.3 00000O00n01U02602702B02T02Y03103903:03;03A03E03P03Q03[S2ra2sp1X1n3cnt2v13xs02zs2LZ2LXS2ra2sp1X1n3cnt2v13xs02zs2LZ2LXS1R3HIA1h2ra2sp1X1n3cnt2v13xs02zs2LZ2LXS1R2ra2sp1X1n3cnt2v13xs02zs2LZ2LXSS2v13Hv12H6S1R2lo3LOS3ALO3ACPS1X1nS1R3HIA1h2sp2lo3TOP4HTOPS2v13Hv1SSS1n2HnS2v1S2v13Hv12V1SS1R2lo3LOS". (* [comment removed for export] *)
    Lemma phase2_walk : forall (mm : mem) (xra xt0 xt1 xt2 xs0_ xs1 xa2 xa3 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      0 <= v1 < 32 -> DINV mm zs -> FRAME mm ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n) xa2 xa3 SB (Z_to_bv 64 v1) xa6 xa7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa42a0) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hv1 (HX & LX & MU & WM & MI & ST & HH & OX) FR. rt_facts.
      lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa42e4] [] 40%N). lx_tree.
      all: lx_same_mem; lx_gc; try clear OQH.
      all: lazymatch goal with
           | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa42e4) _ _ _ _) =>
               (* [comment removed for export] *)
               match goal with K : 0 <= ?v + -1 |- _ => constr_eq v v1; rename K into V1 end;
               eapply (loop2_walk ltac:(clear - V1 Hv1; lia) (Z.to_nat n) n zs (Z_to_bv 64 0) 0 0);
                 [ reflexivity | clear - Hn; lia | clear; lia | clear; lia | clear; lia | clear; lia
                 | exact (conj HX (conj LZ (conj MU (conj WM (conj MI (conj ST (conj HH OX)))))))
                 | exact FR
                 | intros; reflexivity | exact TZ
                 | rewrite lseg_empty, Z.div_0_l; [reflexivity|]; apply Z.pow_nonzero; clear - Hv1; lia
                 | rewrite lseg_empty; clear; lia | clear; lia | clear; lia
                 | rewrite Z.mod_0_l by (apply Z.pow_nonzero; clear - Hv1; lia); reflexivity ]
           | |- _ =>
               (* [comment removed for export] *)
               lx_post; [> exact HX | exact LZ | exact TZ | | .. ];
               rewrite <- VZ;
               first [ match goal with K : 0 <= - ?v |- _ => constr_eq v v1; replace v1 with 0 by (clear - K Hv1; lia); rewrite Z.div_1_r; reflexivity end
                     | match goal with K : 0 <= - ?v |- _ => constr_eq v n; exfalso; clear - K Hn; lia end ]
           end.
      all: match goal with |- ?g => idtac "P2-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithZs.

  Lemma zloop_walk : forall (k : nat) (j : Z) (ys : list word) (mm : mem)
      (xra xt2 xs0_ xs1 xt3 xt4 xt5 xt6 : word) (ep ec ej : Z),
      Z.to_nat (n - j) = k -> n - v0 <= j < n -> 1 <= v0 <= n -> 0 <= v1 < 32 ->
      ep = X + 4 * j -> ec = n - j -> ej = j -> length ys = length xs0 ->
      DINV mm (firstn (Z.to_nat (n - v0)) ys ++ repeat (Z_to_bv 64 0) (Z.to_nat (j - (n - v0))) ++ skipn (Z.to_nat j) ys) ->
      FRAME mm ->
      (forall q : nat, (q < Z.to_nat (n - v0))%nat -> limb32 ys q = limb32 xs0 (q + Z.to_nat v0)) ->
      same_from (Z.to_nat (n - v0)) ys xs0 ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp (Z_to_bv 64 1) (Z_to_bv 64 ep) xt2 xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n)
                 (Z_to_bv 64 ep) (Z_to_bv 64 1) SB (Z_to_bv 64 v1) (Z_to_bv 64 ec) (Z_to_bv 64 ej)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa4248) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros j ys mm xra xt2 xs0_ xs1 xt3 xt4 xt5 xt6 ep ec ej Hk Hj Hv0 Hv1 Ep Ec Ej LY
      (HX & LX & MU & WM & MI & ST & HH & OX) FR HP FS; [exfalso; clear - Hk Hj; lia|].
    subst ec ej. rt_facts.
    lx_limb_rw HX j Ep ltac:(clear - Hj Hv0; lia) ltac:(rewrite LX; clear - Hj Hv0 Ln L0; lia) w NX.
    lx_hide HX. lx_hide MU. lx_hide WM.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4248; 0xa42a0] [(0xa426c, DJoin)] 60%N). lx_tree.
    all: lxr_leaf; lx_unhide; lx_gc.
    all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_aobj X OX'.
    all: match goal with CX' : rw_cells asegs ?m2 ?e [C4 ?vn] |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
           pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(clear - Hj Hv0; lia) Ep MUl WMl CX') as HX' end.
    all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(clear - Ep Hj Hv0 Rv; lia) ltac:(clear - Ep Hj; lia)) as MU'.
    all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: rewrite (shr_zero_step (firstn (Z.to_nat (n - v0)) ys) ys (Z.to_nat (j - (n - v0))) (Z.to_nat j)) in HX'
           by (rewrite ?length_firstn; clear - Hj Hv0 LY Ln L0; lia).
    all: replace (S (Z.to_nat (j - (n - v0)))) with (Z.to_nat (j + 1 - (n - v0))) in HX' by (clear - Hj Hv0; lia).
    all: replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) in HX' by (clear - Hj Hv0; lia).
    all: assert (LX' : length (firstn (Z.to_nat (n - v0)) ys ++ repeat (Z_to_bv 64 0) (Z.to_nat (j + 1 - (n - v0))) ++ skipn (Z.to_nat (j + 1)) ys) = length xs0)
           by (rewrite !length_app, length_firstn, repeat_length, length_skipn; clear - LY Hj Hv0 Ln L0; lia).
    - match goal with K : _ |- _ => assert (BR : j + 1 < n) by (clear - K Hj; lia) end.
      eapply (IH (j + 1) ys);
        [ clear - Hk Hj; lia | clear - Hj BR; lia | exact Hv0 | exact Hv1 | clear - Ep; lia | clear; lia | clear; lia | exact LY
        | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
        | assumption | exact HP | exact FS ].
    - match goal with K : _ |- _ => assert (EJ : j + 1 = n) by (clear - K Hj; lia) end.
      replace (Z.to_nat (j + 1 - (n - v0))) with (Z.to_nat v0) in HX', LX' by (clear - EJ; lia).
      replace (Z.to_nat (j + 1)) with (Z.to_nat n) in HX', LX' by (clear - EJ; lia).
      assert (LA : length (firstn (Z.to_nat (n - v0)) ys) = Z.to_nat (n - v0)) by (rewrite length_firstn; clear - LY Hv0 Ln L0; lia).
      eapply (phase2_walk (firstn (Z.to_nat (n - v0)) ys ++ repeat (Z_to_bv 64 0) (Z.to_nat v0) ++ skipn (Z.to_nat n) ys));
        [ exact LX' | | | exact Hv1 | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX'))))))) | assumption ].
      + rewrite app_assoc, skipn_app, skipn_all2 by (rewrite length_app, repeat_length, LA; clear - Hv0; lia).
        rewrite length_app, repeat_length, LA. replace (_ - _)%nat with 0%nat by (clear - Hv0; lia). rewrite skipn_O.
        cbn [app]. apply same_from_skipn; [| exact LY]. eapply same_from_weaken; [exact FS | clear - Hv0; lia].
      + rewrite (shr_phase1_value xs0 ys n v0) by first [klia | exact HP].
        rewrite Z.div_div, <- Z.pow_add_r by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonneg; klia).
        f_equal. f_equal. klia.
    all: match goal with |- ?g => idtac "ZLOOP-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01O0@C17025492443.120C32557765051.121D16567456097.91 D30773804150.121D5483095183.91  D563007111.92   D60109446735.121D60203142919.121D62022258533.92 D64311484648.121K28766042983.121K37572734504.120K6518702880.120 L11227989955.63 L14790846217.101L14795304323.49 L14815853374.101L14817495809.61 L15267582081.54 L15716906916.54 L15718253958.100L17030591556.51 L17032496742.99 L18928162206.100L18932096788.47 L19145612765.66 L19149367021.50 L19661879783.53 L19662658402.46 L21589195979.53 L21589605492.101L21757942144.50 L21932501679.58 L21934217872.101L25069386524.118L25070161578.68 L26659132285.54 L26662101343.100L26662101343.99 L28121254647.58 L28762393027.4  L29428324939.5  L30784500839.50 L31257571049.50 L32879090465.0  L33620847837.54 L35653441506.7  L35666028354.61 L37443248876.51 L37569264717.5  L38806159341.47 L38810088807.100L39839562448.47 L39843491930.100L39843491930.101L41359420241.50 L41363349979.101L41418351563.50 L43020513267.118L43030600914.70 L46768182562.50 L46772641704.101L4779868151.66  L51692282852.50 L51694064070.99 L53056398486.2  L54399722610.53 L57022275262.47 L57868415478.54 L57902633104.88 L57905070385.45 L59252812109.5  L60096736491.56 L60098763854.3  L62007315621.54 L63566657160.99 L63568037034.50 L64048439862.47 L64052373692.100L6514053445.2   L65575081552.52 N21804655702.121N22841058113.121N37110878770.121N53196997091.121O17025492443.120O174838075.121  O31132687832.120O32557765051.121P6518702880.120 Q14790846217.101Q30773804150.121Q38248387216.121Q43879899724.121Q60203142919.12100000100200G01;01N01i02U03803M04?05=06006106507>07?07@07A07D07E08?08@09409h09i0:50:A0:N0:[0:\0;Y0;a0;b0;c0=80=90=:0=;0=<0=L0=M0=_0=k0>30>40>A0>Y0?50?=0?>0??0@30@40@50@60@70@80@90A60A70A80A90AH0AI0B;0BB0BJ0BK0B[0CC0CD0CE0CO0CY0Cf0DX0DY0DZ0EN0EO0EY0FA0Fl0GT0H80H90H:0H;0HU0HV0IT0J80JV0K70KTFFS2ra2sp1X1n3xs02ys2LXS2ra2sp1X1n2v02lx3xs02Hn2XB3SPR2ys3Hv01A1B2LX2LA3LB'S2ra2sp1X3xs02ys2LXS1R3HIA1h2ra2sp1X3xs02ys2LXS1R2ra2sp1X1n2v02lo3xs03LOS2ys1A1B2LX2LA3LB'S2ra2sp1X1n2v03xs02ys1A1B2LX2LA3LB'S1R2ra2sp1X3xs02ys2LXS1R3HIA1h2ra2sp1X1n2v02lo3xs03TOP2ys1A1B2LX2LA3LB'S1R5NEED02sp1X1n2v02lx2lo3xs02Hn2Ln2LO2SX2ys3Hv01A1B2LX2LA3LB'S2sp1X1n2v02lx2lo3xs02Hn2Ln2SX2ys3Hv01A1B2LX2LA3LB'FS2v0S1R5NEED02ra2sp1X1n2v02lx2lo3xs02Hn2XB3SPR3LOS2LO2ys1A1B2LX3ALO2H02LA3LB'FFFS1RFS2ra2sp1X1n2v02lx3xs02Hn2Ln2L02XB3SPR2ys3Hv01A1B2LX2LA3LB'FS2ra2sp1X1n2v02lx3xs02Hn2Ln2L02XB3SPR2ys1B2LX2LA3LB'S2ra2sp1X1n2v02lx3xs02Hn2XB3SPR2ys3Hv01A1B2LX2LA3LB'FS1X1n2v03Hv0S1X1n2v03Hv0S1n2v02Hn3Hv0S1n2v02Hn3Hv0FS2ra2sp1X1n2v02lx2lo3xs02Hn2Ln2XB3SPR2SX2ys3Hv01A1B2LX2LA3LB'S1X1n2v0FFS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Hn2Ln2L02XB4Hcnt4Ecnt3SPR2SX2ys3Hv03Hv11A1B2LX2LA3LB'FFFFS1R3HIA1h2sp3TOPFS1R2lo3LOS3ALO3ACPS1X1n2v03Hv0S1X1n2v0SS1n2v02Hn3Hv0S1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1h2sp2lo3SPR3TOP4HTOPS2v13Hv1FFS2ra2sp1X1n2v02lx3xs02Hn2XB3SPR2ys3Hv01A1B2LX2LA3LB'FFFFFSS2ra2sp1X1n2v02lx2lo3xs02Hn2Ln2XB3SPR2SX2ys3Hv01A1B2LX2LA3LB'FFFS1X1n2v02Hn3Hv0FS2ra2sp1X1n2v02lx3xs02Hn2XB3SPR2ys3Hv01B2LX2LA3LB'S2sp2loS2v13Hv1SS3cnt2v02v14EcntS2ra2sp1X1n2lx3xs02Hn2Ln2L02XB3SPR2ys2LXFFS1R2lo3LOSS1R2lo3LOSS1n2v02Hn3Hv0S2ra2sp1X1n2v02lx3xs02Hn2XB3SPR2ys3Hv01B2LX2LA3LB'FFS2ra2sp1X1n2v02lx3xs02Hn2XB3SPR2ys3Hv01A1B2LX2LA3LB'FS1n2v03Hv0S2sp1n2v02lo3xs02ys1A1B2LX2LA3LB'3x152C0S1X1n2v03xs02Hn2ys3Hv01A1B2LX2LA3LB'3x152C0S2sp1n2v02lo3xs02ys1A1B2LX2LA3LB'3x152C0S1X1n2v03xs02ys1A1B2LX2LA3LB'3x152C0FFFS1X1n2v02Hn3Hv01A1B2LA3LB'FS1R5NEED02sp1n2v02lo3xs02Hn3SPR3LOS2LO2ys1A1B2LX3ALO2H02LA3LB'S1X1n2v03xs02Hn2ys3Hv01A1B2LX2LA3LB'S1n2v02lo3xs02ys1A1B2LX2LA3LB'S2sp1n2v02lo3xs02ys1A1B2LX2LA3LB'S1X1n2v03xs02ys1A1B2LX2LA3LB'". (* [comment removed for export] *)
  Lemma after_copy_walk : forall (ys : list word) (mm : mem)
      (xra xt0 xt1 xt2 xs0_ xs1 xa2 xa3 xt3 xt4 xt5 xt6 : word),
      1 <= v0 <= n -> 0 <= v1 < 32 -> DINV mm ys -> FRAME mm ->
      (forall q : nat, (q < Z.to_nat (n - v0))%nat -> limb32 ys q = limb32 xs0 (q + Z.to_nat v0)) ->
      same_from (Z.to_nat (n - v0)) ys xs0 ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n) xa2 xa3 SB (Z_to_bv 64 v1)
                 (Z_to_bv 64 v0) (Z_to_bv 64 (n - v0)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa421c) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros Hv0 Hv1 (HX & LX & MU & WM & MI & ST & HH & OX) FR HP FS. rt_facts.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa42a0; 0xa4248] [] 40%N). lx_tree.
    all: try (exfalso; match goal with K : 0 <= - ?a + ?b |- _ => constr_eq b v0; clear - K Hv0; klia end).
    all: lx_same_mem; lx_gc; try clear OQH.
    (* [comment removed for export] *)
    pose proof LX as LY.
    assert (EY : firstn (Z.to_nat (n - v0)) ys ++ repeat (Z_to_bv 64 0) (Z.to_nat (n - v0 - (n - v0))) ++ skipn (Z.to_nat (n - v0)) ys = ys)
      by (replace (Z.to_nat (n - v0 - (n - v0))) with 0%nat by (clear; lia); cbn [repeat app]; apply firstn_skipn).
    (* [comment removed for export] *)
    rewrite <- EY in HX, LX.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply (zloop_walk (Z.to_nat (n - (n - v0))) (n - v0) ys);
      [ reflexivity | clear - Hv0; lia | exact Hv0 | exact Hv1 | clear; lia | clear; lia | clear; lia | exact LY
      | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX)))))))
      | assumption | exact HP | exact FS ].
    all: match goal with |- ?g => idtac "AC-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0@D16569110288.104D5472959230.104 D563007111.105  D62022258533.105L12357781830.4  L13714601152.6  L19828968716.3  L27859920703.8  L28484124318.11 L29428324939.5  L30201247750.5  L31121482974.7  L31836105628.5  L32001960629.4  L35653441506.7  L43896271426.5  L45272753470.4  L51137062959.5  L55185304208.5  L58014812874.7  L59113821860.4  L59308551419.4  L59308586377.5  L59310648470.12 L60098763854.3  L62891341106.7  L65575351509.5  L68255556145.7  00000O00n01U02602A02Q02Y03003R03d04304G04V04a05905G05R05a05o06C06N06\06j07P07Z07m08<08PS2ra2sp1X1n2v03xs01k1j2ys2Hk2LXS2ra2sp1X1n2v03xs01k1j2ys2Hk2LXS1R3HIA1h2ra2sp1X1n2v03xs01k1j2ys2Hk2LXS1R2ra2sp1X1n2v03xs01k1j2ys2Hk2LXS1n2v01j2HjS1n2v01k1j2Hk2HjS1j1q2NES1X1n2v01j2ep2Hj3Hv02EpS1n2v02lx3xs02Ln2L01j2ys2Hj3Hv02LXS1R2lo3LOS3ALO3ACPS1n2v01j2Hj3Hv0S1n2v01j2ec2Hj2Ec2BRS1n2v01j2Hj3Hv0S1X1j2ep2EpS1R3HIA1h2sp2lo3TOP4HTOPS1n2v01j2Hj2EJS1n2v01j2HjS1n2v01j2Hj3Hv0S1n2v01j2ec2EcS1n2v01j2ec2Hj2Ec2H8S1j1q2Hq2NES1j2ys4IBwd2NXS1n2v01j2Hk2HjS1n2v02lx3xs02Ln2L01j2ys2Hj3Hv02LX3NXsS1R2lo3LOSS1X1n2v01j2ep2Hj2EpS1n2v01j2Hj3Hv0S1X2v01j2ep2ev2Ep2Ev". (* [comment removed for export] *)
  Lemma loop1_walk : forall (k : nat) (j : Z) (ys : list word) (mm : mem) (xra xs0_ xs1 xa3 : word) (ep ec ev et0 enx : Z),
      Z.to_nat (n - v0 - j) = k -> 0 <= j < n - v0 -> 1 <= v0 -> 0 <= v1 < 32 ->
      ep = X + 4 * j -> ec = j -> ev = 4 * v0 -> et0 = 4 * j -> enx = 18446744073709551615 - X ->
      DINV mm ys -> FRAME mm ->
      (forall q : nat, (q < Z.to_nat j)%nat -> limb32 ys q = limb32 xs0 (q + Z.to_nat v0)) ->
      same_from (Z.to_nat j) ys xs0 ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp (Z_to_bv 64 et0) (Z_to_bv 64 ec) (Z_to_bv 64 1) xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n)
                 (Z_to_bv 64 ep) xa3 SB (Z_to_bv 64 v1) (Z_to_bv 64 v0) (Z_to_bv 64 (n - v0))
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 enx) (Z_to_bv 64 1) (Z_to_bv 64 ev) (Z_to_bv 64 ep))
            F (Z_to_bv 64 0xa4378) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros j ys mm xra xs0_ xs1 xa3 ep ec ev et0 enx Hk Hj Hv0 Hv1 Ep Ec Ev Et0 Enx
      (HX & LX & MU & WM & MI & ST & HH & OX) FR HP FS; [exfalso; clear - Hk Hj; lia|].
    subst ec et0 enx. rt_facts.
    (* [comment removed for export] *)
    destruct (nth_error ys (Z.to_nat (j + v0))) as [w|] eqn:NXs; [| exfalso; apply nth_error_None in NXs; clear - NXs Hj Hv0 Ln LX L0; lia].
    pose proof (u32ro_cell_at mm X ys (j + v0) (ep + ev) w (u32arr_ro _ _ _ _ HX) NXs ltac:(clear - Hj Hv0; lia) ltac:(clear - Ep Ev; lia)) as CS.
    lx_limb_rw HX j Ep ltac:(clear - Hj; lia) ltac:(clear - Hj Hv0 Ln LX L0; lia) wd NX.
    lx_hide HX. lx_hide MU. lx_hide WM.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa4378; 0xa421c] [(0xa43b0, DJoin); (0xa43c8, DJoin)] 60%N). lx_tree.
    all: lxr_leaf; lx_unhide; lx_gc.  (* [comment removed for export] *)
    all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_aobj X OX'.
    all: match goal with CX' : rw_cells asegs ?m2 ?e [C4 ?vn] |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
           rewrite lx_sx32 in CX';
           pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(clear - Hj; lia) Ep MUl WMl CX') as HX' end.
    all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(clear - Ep Hj; lia) ltac:(clear - Ep Hj Hv0; lia)) as MU'.
    all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    (* [comment removed for export] *)
    all: assert (VW : limb32 xs0 (Z.to_nat (j + v0)) = w32 w) by (apply limb32_nth_error; rewrite <- (FS (Z.to_nat (j + v0))) by (clear - Hj Hv0; lia); exact NXs).
    all: assert (HP' : forall q, (q < S (Z.to_nat j))%nat -> limb32 (upd ys (Z.to_nat j) (sx32 w)) q = limb32 xs0 (q + Z.to_nat v0)%nat)
      by (intros q Hq; destruct (Nat.eq_dec q (Z.to_nat j)) as [->|NE];
          [ rewrite limb32_upd_same, w32_of_sx32, <- VW by (clear - Hj Hv0 Ln LX L0; lia); f_equal; clear - Hj Hv0; lia
          | rewrite limb32_upd_other by (clear - NE; lia); apply HP; clear - Hq NE; lia ]).
    all: pose proof (same_from_upd _ _ _ (sx32 w) FS) as FS'.
    all: assert (LX' : length (upd ys (Z.to_nat j) (sx32 w)) = length xs0) by (rewrite upd_length; exact LX).
    - (* [comment removed for export] *)
      match goal with K : _ |- _ => assert (BR : j + 1 < n - v0) by (clear - K Hj; lia) end.
      eapply (IH (j + 1)); [clear - Hk Hj; lia | clear - Hj BR; lia | exact Hv0 | exact Hv1 | clear - Ep; lia | clear; lia | exact Ev | clear; lia | clear; lia
        | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
        | assumption
        | replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by (clear - Hj; lia); exact HP'
        | replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by (clear - Hj; lia); exact FS' ].
    - (* [comment removed for export] *)
      match goal with K1 : _ |- _ => assert (EJ : j + 1 = n - v0) by (clear - K1 Hj; lia) end.
      eapply (after_copy_walk (upd ys (Z.to_nat j) (sx32 w))); [clear - Hv0 Hj; lia | exact Hv1
        | exact (conj HX' (conj LX' (conj MU' (conj WM' (conj MI' (conj ST' (conj HH OX')))))))
        | assumption
        | replace (Z.to_nat (n - v0)) with (S (Z.to_nat j)) by (clear - EJ Hj; lia); exact HP'
        | replace (Z.to_nat (n - v0)) with (S (Z.to_nat j)) by (clear - EJ Hj; lia); exact FS' ].
    all: match goal with |- ?g => idtac "LOOP1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?D16567456097.89D5483095183.89 D563007111.90  D62022258533.90L20121458545.46L29428324939.5 L29708977330.46L35653441506.7 L35900595797.90L35902902260.43L43202745811.7 L59308587280.2 L59308587280.94L59308587280.96L59315812624.47L60098763854.3 L60291848104.44L65577440092.49L68464304787.4600000B00R00j01<01E01W01]02502e02f03B03H03o04004104;04>04N04WS2ra2sp1X1n3xs02LXS2ra2sp1X3xs02LXS1R3HIA1h2ra2sp1X3xs02LXS1R2ra2sp1X3xs02LXS1n2v02H7S1R2lo3LOS3ALO3ACPS1n2v0S1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3cnt2v02v12lx3xs02XB4Ecnt3SPR3Hv12LX2H8FS3cnt2v02v14Hcnt4Ecnt2Rv3C32S1q2HqS2ra2sp1X1n2v02lx3xs02XB3SPR2LX2H71q2HqFFS1R2lo3LOSS1XS1n2v02Hn3Hv02H7S1n2v02H7". (* [comment removed for export] *)
  Lemma phase1_walk : forall (mm : mem) (xra xt0 xt1 xt2 xs0_ xs1 xa3 xa7 xt3 xt4 xt5 xt6 : word),
      v0 <= n -> v0 < n \/ v1 = 0 -> 0 <= v1 < 32 -> DINV mm xs0 -> FRAME mm ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 xs0_ xs1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt) xa3 SB
                 (Z_to_bv 64 v1) (Z_to_bv 64 v0) xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa420c) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros Hv0 Hdis Hv1 (HX & LX & MU & WM & MI & ST & HH & OX) FR. rt_facts.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa42a0; 0xa4378; 0xa421c] [] 40%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    all: lazymatch goal with
         | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa42a0) _ _ _ _) =>
             (* [comment removed for export] *)
             match goal with K : 0 <= - ?c + 31 |- _ => constr_eq c cnt; rename K into C32 end;
             eapply (phase2_walk xs0); [reflexivity | reflexivity | | exact Hv1
               | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR ];
             f_equal; f_equal; clear - C32 Ecnt Rv Hcnt; lia
         | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa4378) _ _ _ _) =>
             (* [comment removed for export] *)
             eapply (loop1_walk (Z.to_nat (n - v0)) 0 xs0);
               first [ reflexivity | exact Hv1
                     | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR
                     | intros q Hq; exfalso; clear - Hq; lia | apply same_from_refl
                     | klia | f_equal; klia
                     | match goal with |- ?g => idtac "P1-COPY-LEFT:" g end ]
         | |- _ =>
             (* [comment removed for export] *)
             eapply (after_copy_walk xs0);
               first [ exact Hv1
                     | exact (conj HX (conj LX (conj MU (conj WM (conj MI (conj ST (conj HH OX))))))) | exact FR
                     | intros q Hq; exfalso; klia | apply same_from_refl
                     | klia
                     | match goal with |- ?g => idtac "P1-ZT-LEFT:" g end ]
         end.
    all: match goal with |- ?g => idtac "P1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

(* [comment removed for export] *)
Ltac zero_all_sr sp HX HH MU AMS SCS0 :=
  lazymatch type of HX with u32arr asegs ?mc ?X ?xs =>
  lazymatch type of HH with HM asegs ?R ?HIA ?h ?LB ?LF _ =>
  lazymatch type of MU with munch [(_, _ + 4 * ?n); (?lo, _)] _ _ =>
    let EY := fresh "EY" in let LB' := fresh "LB'" in
    pose proof (firstn_skipn (Z.to_nat n) xs) as EY; symmetry in EY;
    assert (LB' : length (firstn (Z.to_nat n) xs) = Z.to_nat n) by (rewrite firstn_length; klia);
    let HXB := fresh "HXB" in let HXC := fresh "HXC" in let HXC0 := fresh "HXC0" in
    rewrite EY in HX; apply u32arr_app in HX; destruct HX as [HXB HXC]; rewrite LB' in HXC;
    apply u32arr_cells in HXB; rewrite LB' in HXB; apply (u8arr_of_rw_cells asegs) in HXB;
    pose proof (lock HXC) as HXC0; clear HXC;
    let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
    pose proof (munch_refl [(X, X + 4 * n); (lo, bv_unsigned sp + -32)] mc) as MU2;
    pose proof (wmono_refl asegs mc) as WM2;
    let SPM := fresh "SPM" in
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_SR) as SPM; rewrite <- AMS in SPM;
    unfold A_ASAN_MEMSET_SR in AMS; rewrite AMS in SPM;
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := X) (v := 0) (n := 4 * n) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by klia;
       try eassumption; try reflexivity; try klia;
       first [ left; reflexivity
             | rewrite u32s_length; klia
             | f_equal; klia
             | eapply crange_sub; [exact SCS0| klia| klia]
             | match goal with CW : client_wrange _ _ _ _ X _ |- _ => eapply (cw_top47_in asegs R HIA h LB LF); [eassumption| exact CW| klia| klia| klia] end     (* [comment removed for export] *)
             | match goal with |- ?g => idtac "MEMSET1-PRE-LEFT:" g end ]);
    clear SPM;
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u32arr_transport asegs _ mc mx _ _ (unlock _ HXC0) MU2 WM2 ltac:(cbn [disjoint_from]; rewrite length_skipn; klia)) as HXC;
      clear HXC0 MU2 WM2;
      match goal with H : u8arr _ mx X _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; rename H into HXB end;
      apply (u32arr_of_cells asegs mx _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat n))) in HXB; [| rewrite u32s_repeat0; f_equal; klia ];
      let HX' := fresh "HX'" in
      assert (HX' : u32arr asegs mx X (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs))
        by (apply u32arr_app; split; [exact HXB|]; rewrite repeat_length;
            lazymatch type of HXC with u32arr _ _ ?a _ => replace (X + 4 * Z.of_nat (Z.to_nat n)) with a by klia end; exact HXC);
      clear HXB HXC
    end end end end.

Local Ltac2 Set LiaOrc.tbl := fun () => "02B0@C17025492443.115C17025492443.119C45137625611.116C45137625611.120D16565017318.81 D16569571680.118D16569571680.122D5472627854.118 D5472627854.122 D5485375240.81  D563007111.82   D60109446735.118D60109446735.122D62022258533.82 D64311484648.118D64311484648.122K15588900467.115K15588900467.119K16123043814.118K16123043814.122K49644543183.116K49644543183.120K6518702880.115 K6518702880.119 L11902153813.48 L14790538089.47 L14790846217.102L14790846217.98 L14815853374.102L14815853374.98 L14815866718.60 L15270278366.53 L15601019926.4  L15736687899.64 L16134275612.3  L22452315093.2  L23778900769.0  L2426788581.62  L251802664.65   L251802664.66   L254637610.49   L254637610.51   L28118707880.57 L28136079014.48 L28136290176.101L28136290176.102L28136290176.97 L28136290176.98 L29428551881.72 L29429056688.43 L29970074883.46 L29970278617.62 L31152452195.102L31152452195.98 L31152891395.51 L31378308326.81 L32745086150.65 L32745086150.66 L32747888324.49 L32747888324.51 L35667657501.60 L35668187074.57 L36459598520.52 L36459598520.54 L39284637285.0  L41418351563.61 L41431410718.62 L43061724204.79 L43781392513.47 L43781598555.63 L44017858037.43 L44238204.67    L44238204.69    L44766484234.52 L44766484234.54 L45544510402.48 L45544846872.64 L46607116463.43 L49582233453.62 L49656466606.3  L50304316348.65 L50304316348.66 L50305544638.49 L50305544638.51 L53056398486.2  L53467004379.46 L53467191297.62 L53814194103.65 L53814194103.66 L53816864181.49 L53816864181.51 L5483969141.47  L55959448093.102L55959448093.98 L55960321661.48 L57017434196.45 L57628691269.113L57628691269.117L58430200549.47 L59906985831.64 L60098234548.55 L60098763883.52 L60745277636.46 L6331589666.70  L6331589666.71  L63554697072.48 L63742606293.2  L6514053445.2   L68369006039.62 L695418636.47   L695605974.63   L9788927037.46  N22834764276.116N22834764276.120N37104593031.116N37104593031.120O17025492443.115O17025492443.119O17223163713.115O17223163713.119O28310886539.118O28310886539.122O36529563484.118O36529563484.122O45137625611.116O45137625611.120O54173095307.117O54173095307.121P22463430191.118P22463430191.122P49644543183.116P49644543183.120P63752726063.117P63752726063.121P6518702880.115 P6518702880.119 Q14790846217.102Q14790846217.98 Q16569571680.118Q16569571680.122Q38248387216.118Q38248387216.122Q43879899724.118Q43879899724.122Q5472627854.118 Q5472627854.122 00000100200300400J00d01>01X02202F02b03E03h04>04g05P06806`07S08F08G08H08I08J08O08P09S0:V0:W0:X0:Y0:\0:]0:m0:n0:o0;00;60;C0;P0;]0;g0<;0<<0<=0<>0<?0<@0<e0<f0<l0=20=a0>P0>Q0>e0>m0?50?=0?E0?a0@=0@K0@Y0@Z0@[0@^0AI0AQ0AY0AZ0Aj0B=0BH0BS0B\0Be0Bf0Bl0Bm0C70CA0CK0CU0C\0Cb0Ch0D20D<0DF0DP0DS0DT0DU0DV0DW0E80EY0Ee0Ej0F40F>0FD0FE0G00G=0G>0G?0GE0GM0GU0G[0G\0G]0G^0G_0G`0Ga0Gb0Gc0Gd0Ge0Gf0Gg0Gh0Gi0Gj0Gk0Gl0Gm0Gn0Go0H00H10H20H30Hi0I_0J60JM0Je0K=0KU0Km0LD0L[FFFFS2ra2sp1X1n3cnt2xs3SPRS2ra2sp1X1n3cnt2xs3SPR3LB'S2ra2sp1X1n3cnt2xs3SPR3LB'S2ra2sp1X1n3cnt2xs3SPR3LB'S2ra2sp1X1n3cnt2xs3SPR3LB'S2ra2sp1X3cnt2xs3SPRS1R3HIA1h2ra2sp1X3cnt2xs3SPRS1R2ra2sp1X1n3cnt2lo2xs3LOS3SPR3LB'S1R2ra2sp1X1n3cnt2lo2xs3LOS3SPR3LB'S1R2ra2sp1X3cnt2xs3SPRS1R3HIA1h2ra2sp1X1n3cnt2lo2xs3TOP3SPR3LB'S1R3HIA1h2ra2sp1X1n3cnt2lo2xs3TOP3SPR3LB'S2sp1X1n3cnt2lo2xs2Hn2LX4Hcnt2SX3SPR3LB'S2sp1X1n3cnt2lo2xs2Hn2LX4Hcnt2SX3SPR3LB'S1R5NEED02sp1X1n3cnt2lo2xs2Hn2LX4Hcnt2LO2SX3SPR3LB'S1R5NEED02sp1X1n3cnt2lo2xs2Hn2LX4Hcnt2LO2SX3SPR3LB'FFFFS1X1nFS1R5NEED02ra2sp1X1n3cnt2lo2xs2Hn4Hcnt3NZX3LOS2LO3SPA3ALO3SPR2H03LB'S1R5NEED02ra2sp1X1n3cnt2lo2xs2Hn4Hcnt3NZX3LOS2LO3SPA3ALO3SPR2H03LB'FFFS1RFS1n2xs2Hn2LX3LB'FFSS1n2HnS3cnt4Hcnt2MBS3cnt4Hcnt2MBS3cnt4Hcnt2MBS3cnt4HcntS1R3HIA1h2sp3TOP3SPRFFFFFS1R2ra2sp1X2lo2xs3NZX3LOS3ALO3ACP3SPRFS1n2HnS1n2HnS2ra2sp1X1n3cnt2lo2xs2Hn2LX4Hcnt3NZX2SX3SPR3LB'S2ra2sp1X1n3cnt2lo2xs2Hn2LX4Hcnt3NZX2SX3SPR3LB'FS2ra2sp1X3cnt2xs3SPRS3cnt2MBS3cnt2MBS3cnt2MBS3cnt2MBS1R3HIA1h2sp2lo3TOP4HTOP3SPRS1R3HIA1h2sp2lo3TOP4HTOP3SPRS1n3cnt2MB3H10S1n3cnt2MB3H10SSS1nS1R5NEED02ra2sp1X3cnt2lo2xs4Hcnt3NZX2LO3SPRS2sp3SPRS2sp3SPRSS1n3cnt4Hcnt3H10S1n3cnt4Hcnt3H112E5S1n3cnt3H10S1n3cnt3H13S1X2xs2XBS1X2xs2XBSS1n2HnFS3cnt4HcntS3cnt4HcntS3cnt4HcntS3cnt4HcntS2sp2loS1n2HnS1n2HnS3cnt4HcntS3cnt4HcntS3cnt4HcntS3cnt4HcntS1XFFFSS2sp1X1n3cnt2lo2xs3SPR3LB'3x152H3S2sp1X1n3cnt2lo2xs3SPR3LB'3x152H3S1n2xs2Hn2LXS1X1nS1R2lo3LOSS1R2lo3LOSS1n2HnFS2sp1X1n2lo2xs2Hn2LX3ALX3NZX3SPA2SX3SPR3LB'S1n2xs2Hn3LB'FFS1n2HnS2sp3SPRS2sp3SPRS1n2HnFFFFFFFFFFFFFFFFFFFFFFFFS1R5NEED02sp1n3cnt2lo2xs2Hn4Hcnt3LOS2LO3ALO3SPR2H03LB'S1R5NEED02sp1n3cnt2lo2xs2Hn4Hcnt3LOS2LO3ALO3SPR2H03LB'S2sp1X1n3cnt2xs3SPR3LB'S2sp1X1n3cnt2xs3SPR3LB'S2sp1n3cnt2lo2xs3SPR3LB'S2sp1n3cnt2lo2xs3SPR3LB'S2sp1n3cnt2lo2xs3SPR3LB'S2sp1n3cnt2lo2xs3SPR3LB'S2sp1X1n3cnt2xs3SPR3LB'S2sp1X1n3cnt2xs3SPR3LB'". (* [comment removed for export] *)
Lemma A_mpi_core_shift_r_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_shift_r ()) "PR,$45.PHIA,(46.$38.R1.)P,(47.(33.R2.))P,(6.$?.(48.R3.)$49.)P,(24.=(2;.R4.))(4:.$38.R5.R4.$4;.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS NEED0. unfold mpi_core_shift_r_stmtA, A_MPI_CORE_SHIFT_R.
  intros until xs. intros HH HX Hn LX Hcnt ALX NZX ST LOS LO TOP SPA SX CWX MI RA OX -> -> ->.
  unfold MPI_CORE_SHIFT_R_STACK_A in *.
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
  pose proof (hm_abase asegs R HIA h LB LF m HH) as ABS.
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x68258; 0xa420c] [] 60%N). lx_tree.
  all: lxr_leaf; lx_carry; lx_gc.
  all: clear HX ABS; lx_rn_u32 X HX; lx_rn_munch MU; lx_rn_wmono WM.
  all: match goal with K : 0 <= ?q ≫ 5 |- _ => idtac | |- _ => idtac end.
  (* [comment removed for export] *)
  all: assert (E5 : cnt ≫ 5 = cnt / 32) by (rewrite Z.shiftr_div_pow2 by (clear; klia); reflexivity);
       rewrite ?E5, ?land_31_mod in *.
  all: lazymatch goal with
       | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa420c) _ _ _ _) =>
           eapply phase1_walk with (v0 := cnt / 32) (v1 := cnt mod 32) (lx := Z.of_nat (length xs));
           lazymatch goal with
           | |- _ /\ _ => repeat (lazymatch goal with |- _ /\ _ => split end); first [exact HX | reflexivity | eassumption | klia]
           | |- _ => idtac end;
           first [eassumption | reflexivity | klia | idtac]
       | |- _ =>
           zero_all_sr sp HX HH MU AMS SCS0;
           eapply tail_walk with (lx := Z.of_nat (length xs)) (v0 := cnt / 32) (v1 := cnt mod 32);
           lazymatch goal with
           | |- _ /\ _ => repeat (lazymatch goal with |- _ /\ _ => split end);
                          first [exact HX' | rewrite app_length, repeat_length, skipn_length; klia | eassumption | klia]
           | |- _ => idtac end;
           lazymatch goal with
           | |- skipn _ _ = skipn _ _ => rewrite skipn_app, repeat_length, skipn_all2 by (rewrite repeat_length; klia); rewrite Nat.sub_diag; reflexivity
           | |- lval _ _ = _ => rewrite lval_repeat0_app by klia; symmetry; apply Z.div_small; split; [apply (proj1 (lval_range xs n ltac:(klia)))|];
                                eapply Z.lt_le_trans; [apply (proj2 (lval_range xs n ltac:(klia)))|]; apply Z.pow_le_mono_r; klia
           | |- _ => first [eassumption | reflexivity | klia | idtac] end
       end.
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

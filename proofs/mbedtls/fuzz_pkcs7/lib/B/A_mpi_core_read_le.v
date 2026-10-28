(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_read_be P_mpi_core_read_le.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts AImgRT A_mpi_core_mul.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0045c9e543d1fbe5 2 53 1 1 4 4 3 1 46 1 66 1 67 1 7 0 1 54 1 57 4 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P006bd41ffdcb9532 0 5 0 1 51 1 55 1 62 1 63 1P007047f370658e96 1 2 4 2 0 1 84 1 4 4 6 1 39 1 49 1 83 1 2 85 1 86 1P010a664b612b2b19 0 5 0 1 51 1 55 1 62 1 63 1P02621bd81d58ae47 0 2 0 1 83 1P03315b5022f102d4 0 5 0 1 60 1 67 1 84 1 85 1P04284a41f8a7e474 0 2 0 1 4 1P0475b29ef8a421b7 1 2 4 2 0 1 83 1 4 4 7 1 40 1 50 1 82 1 2 84 1 85 1P051fbd667487a3cb 0 2 0 1 23 1P0562fff24bd3830d 2 53 1 1 4 3 3 1 66 1 67 1 6 0 1 54 1 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P06a3c9fab4b9a7a8 0 5 0 1 51 1 55 1 62 1 63 1P072b750a0eacc4b9 0 5 0 1 52 1 56 1 65 1 66 1P07bcc5825f88d133 2 53 1 1 4 3 3 1 66 1 67 1 6 0 1 54 1 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P087980c279748ec7 0 5 0 1 54 1 58 1 67 1 68 1P08de754bfd4098b4 0 6 0 1 51 1 52 1 55 1 62 1 63 1P08e72bf26f678a24 0 5 0 1 60 1 67 1 84 1 85 1P09665deb9cc23d71 0 4 0 1 29 1 37 1 60 1P0a3dea378127e7c4 2 68 0 8 0 16 3 16 11 16 64 16 86 16 87 16 88 16 89 16 1 1 4 4 9 1 42 1 52 1 88 1 7 0 1 2 1 68 4 86 1 87 1 89 1 90 4P0b1ebd5dcb7ca6ef 0 5 0 1 7 1 23 1 31 1 54 1P0b72103afd72d754 0 4 0 1 50 1 62 1 63 1P0c4098cdeefabe79 0 5 0 1 54 1 58 1 67 1 68 1P0de1ecd4ccf59d87 0 5 0 1 52 1 56 1 65 1 66 1P0deb31f4d0de4d44 0 5 0 1 60 1 67 1 84 1 85 1P0e00f836aad0ec22 0 5 0 1 54 1 58 1 67 1 68 1P0e54f2abc3ffc110 0 2 0 1 2 1P0e92414d1c1a18a7 0 5 0 1 52 1 56 1 65 1 66 1P0f38efadf8f8e37b 1 1 4 2 0 1 82 1 3 9 1 83 1 84 4P0ffac07d97a88306 0 2 0 1 39 1P104638c7ae7d654e 0 4 0 1 50 1 62 1 63 1P10ed8d938ae1ef6c 0 2 0 1 31 1P110f628c00983cbc 0 2 0 1 39 1P119544d13020d0c3 1 1 4 2 0 1 83 1 3 8 1 84 1 85 4P11aab525534cfcd8 0 5 0 1 60 1 67 1 84 1 85 1P11b30156bdc16815 1 1 4 4 2 1 35 1 45 1 79 1 3 0 1 80 1 81 4P12add64288c83555 0 2 0 1 37 1P1325cf369af899a7 2 62 1 2 4 4 1 1 86 1 88 1 89 1 16 10 0 4 8 4 41 4 51 4 61 4 67 16 68 4 85 4 87 4 90 4 2 91 1 92 1 1 1 4 4 2 1 85 1 87 1 90 1 6 0 4 10 4 86 4 88 4 89 4 91 16P13d31ad50cda6bdd 0 6 0 1 51 1 52 1 55 1 62 1 63 1P141fb04588a093ce 0 2 0 1 2 1P14a8108ae1358a69 0 2 0 1 38 1P150c6a46be59f3f9 0 2 0 1 1 1P1540985b5681a26a 0 3 0 1 17 4 41 1P158d0ad0cfa07171 0 5 0 1 52 1 56 1 65 1 66 1P1687eca339c9cbaa 0 3 0 4 8 1 84 1P183912892aaa2c29 0 4 0 1 50 1 62 1 63 1P18e65b7ed04c6a00 0 2 0 1 34 1P196cee8c51dbdbf0 0 5 0 1 52 1 56 1 65 1 66 1P19d8cca8a4709c9e 0 2 0 1 3 1P19df9116cfc03c12 1 1 4 4 2 1 35 1 45 1 79 1 3 0 1 80 1 81 4P1ac3749e291567fd 0 3 0 1 31 1 35 1P1cff552cc23c5544 0 2 0 1 2 1P1d0ac1c65f3e38e5 0 2 0 1 32 1P1d7828021e1f2005 0 2 0 1 4 1P1d7d4f6f774148f0 0 3 0 1 28 1 32 1P1dc35eb62d16d4c5 1 1 4 2 0 1 65 1 3 34 1 66 1 67 4P1dd31f4fa9764dc9 0 5 0 1 51 1 55 1 62 1 63 1P1e46a6119900b74c 0 2 0 1 84 1P1e7e1c074dfa2cbf 0 5 0 1 51 1 55 1 62 1 63 1P1edf0f5b1439456e 1 1 4 2 54 1 65 1 3 0 1 66 1 67 4P1eeecffd418f328c 0 5 0 1 52 1 56 1 65 1 66 1P1f36061736fa76e6 0 2 0 1 3 1P1fec9c7383fafeb2 1 1 4 2 0 1 65 1 3 34 1 66 1 67 4P2000cf36fe128f99 0 5 0 1 51 1 55 1 62 1 63 1P206a4a0a182ee25e 1 1 4 2 0 1 83 1 3 8 1 84 1 85 4P206fdb437670c52a 2 53 1 1 4 4 3 1 46 1 66 1 67 1 7 0 1 54 1 57 4 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P217434be91ec7aed 0 2 0 1 2 1P2228f65f088e41d9 1 1 4 2 0 1 83 1 3 8 1 84 1 85 4P234ed6dd053e8b9c 2 53 1 1 4 4 3 1 46 1 66 1 67 1 7 0 1 54 1 57 4 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P23c19b19924d48ae 0 7 0 16 6 4 39 4 49 4 54 16 65 16 83 4P24b91ab7ef8a4333 2 53 1 1 4 4 3 1 46 1 66 1 67 1 7 0 1 54 1 57 4 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P2515d4eda46c0751 0 5 0 1 51 1 55 1 62 1 63 1P25a8ba2ab8e9648d 0 5 0 1 54 1 58 1 67 1 68 1P25ca2b9e4bb4acf2 0 2 0 1 38 1P260ed66c48585a4f 1 1 4 2 0 1 65 1 3 34 1 66 1 67 4P26913b3578012629 1 2 4 2 0 1 84 1 4 4 6 1 39 1 49 1 83 1 2 85 1 86 1P2800fcdac41c4357 0 2 0 1 32 1P2810beefbcf3d987 0 2 0 1 1 1P2825e35dec2fd349 0 5 0 1 51 1 55 1 62 1 63 1P2866a30b311a5c52 0 5 0 1 6 1 8 1 29 4 49 1P286953924236fab3 1 2 4 2 0 1 84 1 4 4 6 1 39 1 49 1 83 1 2 85 1 86 1P286aaea261fea6db 0 5 0 1 52 1 56 1 65 1 66 1P28779f821720374c 0 6 0 1 51 1 52 1 55 1 62 1 63 1P294843b0bbd48fca 0 2 0 1 1 1P29f6392a82dc88f4 0 2 0 1 34 1P29fd9649bd13ac21 1 1 4 2 0 1 79 1 3 4 1 80 1 81 4P2a9e49b375ee0c3e 0 2 0 1 39 1P2d86102c6bccf0f5 0 6 0 1 51 1 52 1 55 1 62 1 63 1P2dc3a4afd93471d1 0 4 0 4 38 1 63 4 64 1P2e1d7b7862c6bba6 0 5 0 1 51 1 55 1 62 1 63 1P2e3009c4b3a34db0 0 5 0 1 52 1 56 1 65 1 66 1P2e65a2da05ec1405 0 5 0 1 60 1 67 1 84 1 85 1P2e8ccea58a184ceb 0 2 0 1 83 1P2e9a88c47640546e 0 7 0 64 1 64 8 64 66 64 67 64 68 64 69 64P2ef67aa67f86f46b 2 53 1 1 4 3 3 1 66 1 67 1 6 0 1 54 1 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P2f84778bb014b4cf 0 5 0 1 52 1 56 1 65 1 66 1P2f95939f31637ed6 0 2 0 1 63 1P2fb918ea79976271 0 5 0 1 6 1 8 1 29 4 49 1P3055a9ce9034c231 0 5 0 1 52 1 56 1 65 1 66 1P306389d8a8524ff2 0 5 0 1 54 1 58 1 67 1 68 1P306f492215f69769 0 2 0 1 39 1P3172fb9cfba6551b 0 2 0 1 33 1P3197b361b4e7a6cd 0 2 0 1 34 1P329cdae002a59a7c 0 6 0 1 9 1 25 1 30 1 33 1 56 1P34b00f008aee964b 0 2 0 1 1 1P34e0709d8c4091d3 2 53 1 1 4 3 3 1 66 1 67 1 6 0 1 54 1 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P3563f312c6fe1884 0 5 0 1 52 1 56 1 65 1 66 1P360072df107c930f 0 5 0 1 54 1 58 1 67 1 68 1P363354a33ba239d4 0 2 0 1 62 1P36e31b2f828773c8 0 2 0 1 31 1P372c07d8e55a95c3 0 6 0 1 51 1 52 1 55 1 62 1 63 1P3759f82e7e86859e 0 4 0 1 50 1 62 1 63 1P3792963440f8e36f 0 5 0 1 51 1 55 1 62 1 63 1P37ba38852f29d055 0 2 0 1 4 1P38083dbb5f3a8e09 0 5 0 1 52 1 56 1 65 1 66 1P38969b9850098964 0 4 0 1 50 1 62 1 63 1P38b9323d42550fd5 1 1 4 4 2 1 35 1 45 1 81 1 8 0 4 5 4 50 16 61 16 79 4 80 4 82 4 83 16P394b4aca550becdb 0 2 0 1 22 1P39538dcf1dff968a 1 1 4 3 0 1 79 1 81 1 5 4 4 7 4 80 4 82 4 83 16P39d23973374bb011 0 2 0 1 1 1P3a74f4a2058b5c5c 0 2 0 1 34 1P3a8db5ffeff818f2 2 53 1 1 4 4 3 1 46 1 66 1 67 1 7 0 1 54 1 57 4 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P3add805e472fcfb0 0 2 0 1 38 1P3b587de8bed82ce9 0 2 0 1 35 1P3bbe88bdfac3e11a 0 5 0 1 60 1 67 1 84 1 85 1P3dd4ba786e711c12 0 2 0 1 34 1P3e6c2c7c50f113d2 1 1 4 3 0 1 82 1 84 1 5 9 4 12 4 83 4 85 4 86 16P3e879c2f33dfdc33 2 53 1 1 4 3 3 1 66 1 67 1 6 0 1 54 1 58 1 65 1 68 1 69 4 1 1 4 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 4P3ee76bdc5ca706de 1 1 4 2 0 1 83 1 3 8 1 84 1 85 4P3f30a35b1e2340d1 0 4 0 4 39 1 62 4 65 1P3f5f0ef6cec31d3d 1 1 4 2 0 1 79 1 3 4 1 80 1 81 4P3f6860c81202bf81 1 1 4 3 0 1 54 4 84 1 6 6 1 39 1 49 1 65 4 83 1 85 4N00dff638e1da1cfaN015a2774c35f7ed8N017b232e95f466c2N03355d1387766a26N03355d60c4ea1757N03362864e5800993N036383b3f94af0d2N042959ddb3be9085N04c48e7551acde99N04cac15b6c3ca6ebN05d68c53644b119aN06326b8fb1e7ba8bN06e9c49b50539b9eN0775f006e9295114N0802f93318ef1f6bN080394c8faf8a640N09e380e84df4bb22N09fad3788129c26bN0a5c97dd20006f38N0aea546a60b10f6dN0b0b9cfcc9d526a2N0b1cbf759981eebcN0b52602326ce0c0fN0c13180db9f105a2N0d4cd0780109a085N0d9639722879de10N0f097d353a96d38dN0fae7e75a12554a0N0fd9e0a68177a671N10b1c16f55972b4eN11617de01b949128N11f5a0e8fa2f3778N1230d8635620a3e3N125371b54845ce2aN127436e3c089c984N12a4748e9b840f9dN133f8851855673c4N151b886690be0d78N159f0b3400646143N15b03d31cdbb4e6cN16d02fbc33642701N16f5e2a7f0f49495N17681514cca8906cN17fde183736f926fN18f8946689e4337eN193a386be6f7301aN1977d65e1ed0be44N19b0308bd157418dN19b476b89a57c81eN19cab4f8fddccf1aN1b3c10e5a03ab27eN1bf91445399f5e02N1cdd70e84168f261N1d81ba08c7823427N1db01b0f51bd0ce2N1dc08a8950ad2382N1eb4d478c1be1c96N1f3f6268563a3157N1f6d77afe89c329fN20cdabad1e95cdbcN20e5022cc2eb46c7N211e51c630440070N21b7748db30063c2N21bbff9ca5afaf61N22026d17f8459e69N220f48aa42292bfdN22f0284d639bb1eaN2313c3f5afc04bb6N23b340b952ebea26N24eeb96faebca181N254a01263d1b8475N264f431a64dd73c4N26a24a03f3ed5925N26f2f95c90dec461N280ac420e4209205N28492b17aa0eb768N2873d321c33b3a8fN29f01f0bfc654ecaN2bc0b594c1481528N2bd9f9bd021fea76N2be3318546371616N2c84bf6ab41104b1N2d1a7a5fe71ef8b0N2d79364288b9e80fN2db432d815a197d3N2dc82614154ccb96N2e55f37f0df3641cN2e69e409964f3e92N2ea31a7bad22d994N2ef3acccf592e250N2f12df2df3b70b8cN2f51d2f1b6980997N30b06e19077ea46fN30efba17cb3a0072N3143312a619823c6N31707283486eba67N318590dd62c824c9N31ded90917bff73aN31ef9894332ea26cN31f9791fa60a3ec3N3213a5551f19beb7N322aed9924481c45N32e145915b118a6cN344abbf8e7e37a40N35235213e2372fc1N35327d207fb864ccN35dc532d5c1df13bN35df3e14eaaaf7c7N3632780fd6044e37N36c32b0a4cc4cfbfN37a3583283c5e3bbN37bbe071d84d4345N37caf5563bd2b6d4N392980696c90f1e1N392e9d42cced8dbaN396500044c8f0a74N39c2fc5133a41acdN3b8706b71dc7ff93N3c1f74e1c440c75bN3c7137ca0021253bN3cb22b38bac5d156N3cbe650a35966687N3daf7ec8ce8d004aN3db83fa011aa260aN3de4589c49501647N3faaad3b35bbf3df"%lxh.
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
Ltac2 gd_tbl_A_mpi_core_read_le () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_READ_LE_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_read_le_postA"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_read_be.read_be_ret"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mul.A_ASAN_MEMSET"; "mpi_core_read_le_stmtA"; "A_MPI_CORE_READ_LE"].


Definition A_MPI_CORE_READ_LE : Z := 0xa3c78.
Definition MPI_CORE_READ_LE_STACK_A : Z := 48.

Definition mpi_core_read_le_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n r : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_read_le ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O18.O17.O16.O15.R10.R?.R>.O14.O13.(9.&40.O4.)R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(:.O18.)O7.(;.(2.&40.))R2.(<.O1>.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.O6.(12.O6.(13.+4.O5.)))(>.(?.$10.$10.)(11.$10.$10.O2.(14.&40.O17.))(15.(?.$10.$10.))))O1.R2.)(5.(16.O1>.O1.R2.)(5.(17.O1>.R2.)(5.(18.O1>.R2.O6.R1.)(5.(6.$19.(1:.(2.&40.)R1.)(1:.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1;.(2.&40.)(1<.O5.)R1.)(1;.(2.&40.)(1<.O5.)O3.))(5.(1=.O1>.R2.O2.(14.&40.O17.))(1>.O1>.O1=.O1<.O1;.O1:.O19.R2.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_read_le_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_read_le ()) "Ph,(1?.O4.O3.O2.)PLB,(4.$20.)PLF,(4.$20.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$10.Pn,$10.PB,$10.Pblen,$10.Plo,$10.Pxs,(4.(2.&40.))Pbs,(4.(2.&8.))P,(1>.O4.O3.O2.R2<.R2;.R2:.R8.)P,(18.O4.R9.R8.R3.)P,(22.O4.R:.R7.R3.)P,(5.(23.=R9.)(23.R9.+2710.))P,(23.R:.(24.(1:.(2.&40.)R6.)))P,(5.(23.=R9.)(23.R9.(24.(1:.(2.&8.)R6.))))P,(25.(23.(12.R;.(24.(1:.(2.&8.)R7.)))R=.)(23.(12.R=.(13.+4.(24.(1:.(2.&40.)R8.))))R;.))P,(6.$10.(26.R>.+4.)=)P,(27.R?.(28.+2.+40.))P,(25.(6.$10.R=.=)(27.=R>.))P,(1=.O4.R12.R=.(14.&40.R32.))P,(23.(29.O3.)R>.)P,(23.R?.(2:.(2:.(14.&40.R34.)$2;.)(2<.O3.)))P,(23.(14.&40.R35.)(2=.O4.O3.O2.R39.))P,(6.$10.(26.(14.&40.R36.)+10.)=)P,(25.(23.(12.R16.(13.+4.(24.(1:.(2.&40.)R11.))))R12.)(23.(14.&40.R37.)R16.))P,(25.(23.(12.R15.(24.(1:.(2.&8.)R11.)))R13.)(23.(14.&40.R38.)R15.))P,(2>.(2?.O3.)(30.$20.R3<.(31.R3;.))(29.O3.)(2=.O4.O3.O2.R3=.)R18.(13.+4.R17.))P,(17.O4.R1:.)P,(6.$10.(26.(14.&40.R3<.)+2.)=)P,(32.O4.(33.O3.)(34.O4.O3.O2.R40.)R1<.R1;.(13.+4.R1:.))P,(32.O4.(33.O3.)(34.O4.O3.O2.R41.)R1=.R1:.R19.)P,(6.(2.&40.)R36.(9.&40.R1=.))P,(6.(2.&40.)R36.(9.&40.R1=.))P,(6.(2.&40.)R36.(9.&40.R1=.))P,(6.(2.&40.)R36.(9.&40.R1=.))(35.O4.(33.O3.)(34.O4.O3.O2.R46.)(36.O4.O3.O2.R46.R45.R44.R43.R42.R41.R40.R3<.R3;.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R24.R23.R21.R20.(37.R20.R1>.)R1<.R1=.R22.)(7.(8.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R24.(9.&40.O1.)R23.(;.(2.&40.))R22.(<.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET.
  Hypothesis NEED0 : 0 <= arl_need_amem R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n B blen lx lb lo : Z) (xs0 : list word) (bs : list byte) (junk : list byte).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LB' : Z.of_nat (length bs) = lb.
  Hypothesis Hbl : 0 < blen <= lb.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis BB : 0 < B /\ B + lb <= 2^64.
  Hypothesis DB : B + lb <= X \/ X + 4 * lx <= B.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 48 - arl_need_amem R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SB0 : B + lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis OK : chars_to_limbs4 blen <= n.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X (4 * n).
  Hypothesis HB0 : bytes_at asegs m B bs.

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

  Notation POST := (mpi_core_read_le_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n (read_be_ret n blen) xs0 lo m).
  Notation W := [(X, X + 4 * n); (lo, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation DINV mm xs := (u32arr asegs mm X xs /\ Z.of_nat (length xs) = lx /\ same_from (Z.to_nat n) xs xs0
                          /\ munch W m mm /\ wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -48)
                          /\ HM asegs R HIA h LB LF mm).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2977899845.5800000LS2ra2sp1X1n4blen3xs02bs2OK1E". (* [comment removed for export] *)
  Lemma ret_ok : read_be_ret n blen = 0.
  Proof. unfold read_be_ret. destruct (n <? chars_to_limbs4 blen) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39016585212.600000BS1n4blen2lb3Hbl2OK". (* [comment removed for export] *)
  Lemma blen4 : blen <= 4 * n.
  Proof. clear - OK Hbl Hn. unfold chars_to_limbs4 in OK. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@D16564982518.97 D5485602584.97  D563007111.98   D62022258533.98 L12863407342.7  L12863407343.7  L18575840181.96 L18576006449.54 L18576006449.55 L21993495684.9  L28498816157.5  L29428324939.5  L35653441506.7  L36241682718.83 L39172636981.0  L39758742753.120L45726410883.4  L60098763854.3  L61130118021.12000000Q01001W02802R02l04:04;04<04_04o05A05Y08W08X09J09X09b0:TS2ra2sp1X1n4blen3xs02bs1k1i2xs2HkS2ra2sp1X4blen3xs02bs1k1i2xs2HkS1R3HIA1h2ra2sp1X4blen3xs02bs1k1i2xs2HkS1R2ra2sp1X4blen3xs02bs1k1i2xs2HkS1n4blen1i2Hi3BL44lxv13H16S1n4blen1i2Hi3BL44lxv13H15S1R5NEED02ra2sp1X1n1B4blen2lx2lb2lo3xs02bs2Ln2XB2DB3SPR2LO2SX3SB01k1i2xs2Hk2HiFFS2lx3xs02L01i2xs4lxv14lxv34lxv53LX'S4blen1k1i2Hk2HiS1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA5NEED01h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1n1B4blen2lx2lb2lo3xs02bs3LB'3Hbl2XB2DB3SPR2LO2SX3SB01i2xs2mm3xra3xt03xt13xt23xa13xa73xt33xt43xt53xt62Hk2Hi2LXSS2ra2sp1X4blen3xs02bs1k1i2xs2Hk4lxv14lxv34lxv53H14S4blen1i2Hi2BRS1R2lo3LOSS2ra2sp1X4blen3xs02bs1k1i2xs2Hk4lxv14lxv34lxv53H14". (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i : Z) (xs : list word) (mm : mem)
      (xra xt2 xa1 xt3 xt4 xt5 xt6 wi8 wpb wcnt wnx : word),
      Z.to_nat (blen - i) = k -> 0 <= i < blen ->
      wi8 = Z_to_bv 64 (8 * i) -> wpb = Z_to_bv 64 (B + i) -> wcnt = Z_to_bv 64 (blen - i) ->
      wnx = Z_to_bv 64 (18446744073709551615 - X) ->
      DINV mm xs -> FRAME mm -> aobj asegs AL CS mm X (4 * n) -> aobj asegs AL CS mm B blen ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp (Z_to_bv 64 1) wpb xt2 SB (Z_to_bv 64 B) wpb xa1 wcnt wi8 (Z_to_bv 64 i)
                 (Z_to_bv 64 X) wnx (Z_to_bv 64 B) (Z_to_bv 64 X) (Z_to_bv 64 blen) s4 s5 s6 s7 s8 s9 s10 s11
                 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa3cfc) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i xs mm xra xt2 xa1 xt3 xt4 xt5 xt6 wi8 wpb wcnt wnx Hk Hi -> -> -> ->
      (HX & LX & FX & MU & WM & MI & ST & HH) FR OX OB; [lia|]. rt_facts.
    pose proof blen4 as BL4.
    pose proof (bytes_at_transport asegs _ _ _ _ _ HB0 MU ltac:(cbn [disjoint_from]; rewrite LB'; klia)) as HB.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa3cfc] [(0xa3d1c, DJoin); (0xa3d48, DJoin)] 60%N). lx_tree.
    all: lxr_leaf; lx_carry; lx_gc.
    all: match goal with H1 : u32arr asegs ?m2 X (upd ?xs1 (Z.to_nat (?q ≫ 2)) ?v), K : 0 <= ?i1 + - ?q |- _ =>
           rename H1 into HX';
           assert (LX' : Z.of_nat (length (upd xs1 (Z.to_nat (q ≫ 2)) v)) = lx) by (rewrite upd_length; exact LX);
           assert (FX' : same_from (Z.to_nat n) (upd xs1 (Z.to_nat (q ≫ 2)) v) xs0)
             by (apply same_from_upd_lt; [exact FX | rewrite Z.shiftr_div_pow2 by (clear; lia); clear - K Hi BL4; lia]);
           lx_rn_munch MU'; lx_rn_wmono WM'; lx_rn_mi MI'; lx_rn_stk ST' end.
    - (* [comment removed for export] *)
      match goal with K : 0 <= - i + (blen + -2) |- _ => rename K into BR end.
      eapply (IH (i + 1)); [clear - Hk Hi; lia | clear - Hi BR; lia | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia
        | exact (conj HX' (conj LX' (conj FX' (conj MU' (conj WM' (conj MI' (conj ST' HH))))))) | exact FR | assumption | assumption].
    - (* [comment removed for export] *)
      rewrite ret_ok. lx_post; [> exact HX' | clear - LX' L0; lia | apply same_from_skipn; [exact FX' | clear - LX' L0; lia] | .. ].
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "01_0@C17025492443.124C45137625611.125C45137625611.126D16565017318.93 D16569571680.128D5472627854.128 D5485375240.93  D563007111.94   D60109446735.128D62022258533.94 D64311484648.128K15588900467.124K16123043814.128K49644543183.125K49644543183.126K6518702880.124 L11901686152.50 L12736239183.65 L14633274262.49 L14790538089.48 L14790846217.106L14815853374.106L14815853374.108L14815866718.61 L15270278366.54 L15601019926.4  L16134275612.3  L21097429411.63 L21104654755.120L22452315093.2  L26171494738.48 L27073384603.4  L28118707880.58 L28135547872.50 L29428551881.77 L29429056688.44 L30018746656.48 L31127190050.46 L31129863708.102L31152292830.53 L31152452195.107L31378308326.94 L34746411592.48 L35144635169.0  L35667657501.61 L35668187074.58 L37468808905.5  L39016714998.5  L39172636981.0  L41015926275.3  L43059596331.92 L48441962885.100L48441962885.103L48442018229.48 L49161362620.3  L49656466606.3  L51733939351.46 L51736377513.102L51736377513.103L53056398486.2  L53471949454.45 L5483503528.49  L55315076415.120L55321253183.63 L55959448093.106L55959448093.108L55959853984.50 L56526853830.49 L57017434196.46 L57519689234.80 L57628691269.121L58430200545.46 L58710375227.5  L59836247768.1  L59906985831.65 L60098234548.56 L60098763883.53 L60745277636.47 L60962026021.102L60962026021.103L60963261979.45 L61086206625.104L61086206625.108L61086523073.50 L6331589666.72  L6331589666.73  L63552601673.47 L63742606293.2  L6514053445.2   L68369006039.62 L8504542741.3   L9788927037.47  N22834764276.125N37104593031.125O17025492443.124O17223163713.124O28310886539.128O36529563484.128O45137625611.125O45137625611.126O54173095307.127P22463430191.128P49644543183.125P49644543183.126P63752726063.127P6518702880.124 Q14790846217.108Q16569571680.128Q38248387216.128Q43879899724.128Q5472627854.128 00000100200300K00c01;01S02302T02n03U04304\04]04^04_04d05005@05A06906:06;06<06?06@06A06B06b06c06l07907M07[08B08C08L08M09409509a0:90:?0:@0:\0;80;I0;[0;\0;f0<b0<c0<d0<e0=20=30=40=50=60==0=@0=C0=`0=a0=b0=c0=d0>10>20?Q0@00@<0@Q0@T0@Y0@c0@m0A30A40A50A60A70A80A90A:0Ae0B40B50B60B90BF0BL0BM0BN0BO0BP0BQ0BR0BS0BT0BU0BV0BW0BX0BY0BZ0CF0C[0D10DG0D\FFFS2ra2sp1X1n2xs2bs3SPR2LPS2ra2sp1X1n2xs2bs3SPR2LPS2ra2sp1X1n2xs2bs3SPR2LPS2ra2sp1X1n2xs2bs3SPR2LPS1R3HIA1h2ra2sp1X1n2xs2bs3SPR2LPS1R2ra2sp1X1n2lo2xs2bs3LOS3SPR2LPS1R2ra2sp1X1n2xs2bs3SPR2LPS1R3HIA1h2ra2sp1X1n2lo2xs2bs3TOP3SPR2LPS2sp1X1n2lo2xs2bs2LX2SX3SPR2LPS1R5NEED02sp1X1n2lo2xs2bs2LX2LO2SX3SPR2LPFFFS1X1nS1n2xs2LX2LPS4blen2bs3Hbl2H9FS1R5NEED02ra2sp1X1n2lo2xs2bs3LOS2LO3SPA3ALO2XB3SPR2LP2H0FFFS1RFFFS2ra2sp1X1n2xs2bs2XB3SPR2LP1q2HqFS4blen2H9S1X2xs2XB3H11S1R3HIA1h2sp3TOP3SPRS1n2xs2LP4LXB8S1R2ra2sp1X2lo2xs2bs3LOS3ALO3ACP2XB3SPRFS4blen2H9FS2ra2sp1X1n1B4blen2xs2bs3NZB3BB03SPR2H9FS2ra2sp1X1n2lo2xs2bs2LX3ALX3SPA2SX2XB3SPR2LPS2ra2sp1X1n2xs2bs3SPR2LPS4blenSS1R3HIA1h2sp2lo3TOP4HTOP3SPRS1R3HIA1h2sp2lo3TOP4HTOP3SPRS1n4blen3H112E21ES1n4blen2bs3Hbl2GESS1n2xs3LX'S1R5NEED02ra2sp1X1n1B2lo2xs2bs2LX2DB2LO2SX2SB2XB3SPR2LP4LXB8FFFS4blen2bs3HblFFFFS2sp2loS1BS1XS2ra2sp1X1n2xs2bs3SPR2LP1q2HqFFFFS1X2xs2XB3H12SS1R5NEED02ra2sp1X1n1B4blen2lo2xs2bs2Hn2LX3Hbl2DB3ALX2XT3NZB3LOS2LO3SPA2SX2SB3ALO3ACP2XB3BB03SPRS2sp1X1n2lo2xs2bs3SPR2LP3x152H3S1n2xs2Hn2LXS1n4blen3H122E21E3H13S1nS1X1nS1R2lo3LOSS1R2lo3LOSS1n2HnFFFFFFFS2sp1X1n2lo2xs2LX3ALX3SPA2SX2XB3SPR2LP4LXB8S1n2xs2Hn2LX2LPFFS1nS4blen2bs3HblS1n2HnFFFFFFFFFFFFFFS1R5NEED02sp1n2lo2xs2bs3LOS2LO3ALO3SPR2LP2H0S2sp1X1n2xs2bs3SPR2LPS2sp1n2lo2xs2bs3SPR2LPS2sp1n2lo2xs2bs3SPR2LPS2sp1X1n2xs2bs3SPR2LP". (* [comment removed for export] *)
Lemma A_mpi_core_read_le_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_read_le ()) "PR,$3?.PHIA,(40.$38.R1.)P,(41.(33.R2.))P,(6.$10.(42.R3.)$43.)P,(23.=(2<.R4.))(44.$38.R5.R4.$45.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS NEED0. unfold mpi_core_read_le_stmtA, A_MPI_CORE_READ_LE.
  intros until bs. intros HH HX HB Hn LX Hbl DB ALX XT NZB ST LOS LO TOP SPA SX SB CWX MI RA OX OB -> -> -> ->.
  unfold MPI_CORE_READ_LE_STACK_A in *.
  pose (lxi := lxA_img (arl_AL R) IMG).
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
  pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (bytes_at_bound _ _ _ _ HB) as BB0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by klia.
  assert (BLT : 0 <= blen < 2^64) by lia.   (* [comment removed for export] *)
  assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| klia| klia]).
  pose proof (munch_refl [(X, X + 4 * n); (lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (lock HB) as HB00.
  pose proof (hm_abase asegs R HIA h LB LF m HH) as ABS.
  (* [comment removed for export] *)
  pose proof (firstn_skipn (Z.to_nat n) xs) as EY. symmetry in EY.
  assert (LP : length (firstn (Z.to_nat n) xs) = Z.to_nat n) by (rewrite length_firstn; klia).
  pose proof HX as HXfull.
  rewrite EY in HX. apply u32arr_app in HX. destruct HX as [HXB HXC]. rewrite LP in HXC.
  apply u32arr_cells in HXB. rewrite LP in HXB. apply (u8arr_of_rw_cells asegs) in HXB.
  pose proof (lock HXC) as HXC0. clear HXC.
  assert (LXB8 : Z.of_nat (length (u32s (firstn (Z.to_nat n) xs))) = 4 * n) by (rewrite u32s_length, firstn_length; klia).
  assert (CR : 0 <= chars_to_limbs4 blen <= blen) by (unfold chars_to_limbs4; clear - Hbl; lia).
  carve_frame 48%nat ST.
  clear HB.
  (* [comment removed for export] *)
  lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x68258] [] 60%N). lx_tree.
  all: lxr_leaf; lx_carry; lx_gc.
  all: match goal with
       | K : 0 <= - ?n' + (?bl ≫ 2 + _) |- _ =>
           assert (E2 : bl ≫ 2 = bl / 4) by (rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity);
           assert (LT8 : n < chars_to_limbs4 blen) by (pose proof (chars_to_limbs4_eq blen ltac:(clear - Hbl; lia)) as E; clear - K E E2; lia);
           clear K E2; assert (R8 : read_be_ret n blen = -8) by (unfold read_be_ret; rewrite (proj2 (Z.ltb_lt _ _)) by exact LT8; reflexivity)
       | K : 0 <= ?n' + (- (?bl ≫ 2) + - _) |- _ =>
           assert (E2 : bl ≫ 2 = bl / 4) by (rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity);
           assert (GE : chars_to_limbs4 blen <= n) by (pose proof (chars_to_limbs4_eq blen ltac:(clear - Hbl; lia)) as E; clear - K E E2; lia);
           clear K E2; assert (R0 : read_be_ret n blen = 0) by (unfold read_be_ret; rewrite (proj2 (Z.ltb_ge _ _)) by exact GE; reflexivity)
       end.
  (* [comment removed for export] *)
  all: try (lazymatch goal with R8' : read_be_ret _ _ = -8 |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
              rewrite R8'; lx_post; [> eassumption | reflexivity | reflexivity | .. ] end).
  all: try (lazymatch goal with R0' : read_be_ret _ _ = 0 |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
              match goal with K : 0 <= - ?X' |- _ =>
                rewrite R0'; replace (Z_to_bv 64 X') with (Z_to_bv 64 0) by (f_equal; clear - K XB; lia) end;
              lx_post; [> eassumption | reflexivity | reflexivity | .. ] end).
  (* [comment removed for export] *)
  assert (BL4 : blen <= 4 * n) by (clear - GE Hbl; unfold chars_to_limbs4 in GE; lia).
  clear HXfull.
  match goal with K : aobj _ _ _ _ X ?n4 |- _ => replace n4 with (4 * n) in K by (clear; lia) end.
  clear HXB ABS. lx_rn_munch MU. lx_rn_wmono WM.
  pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET) as SPM. rewrite <- AMS in SPM. unfold A_ASAN_MEMSET in AMS. rewrite AMS in SPM.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := X) (v := 0) (n := 4 * n) (lo := lo);
     rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by klia;
     try eassumption; try reflexivity; try klia;
     first [ left; reflexivity | rewrite u32s_length, length_firstn; klia | f_equal; klia
           | eapply crange_sub; [exact SCS0| klia| klia]
           | eapply (cw_top47_in asegs R HIA h LB LF); [eassumption| exact CWX| klia| klia| klia]     (* [comment removed for export] *)
           | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
  clear SPM.
  lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  match goal with MU5 : munch _ m m5, WM5 : wmono _ m m5 |- _ =>
    pose proof (u32arr_transport asegs _ m m5 _ _ (unlock _ HXC0) MU5 WM5 ltac:(cbn [disjoint_from]; rewrite length_skipn; klia)) as HXC end.
  match goal with H : u8arr _ m5 X _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; rename H into HXB' end.
  apply (u32arr_of_cells asegs m5 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat n))) in HXB'; [| rewrite u32s_repeat0; f_equal; klia ].
  assert (HX : u32arr asegs m5 X (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs)).
  { apply u32arr_app. split; [exact HXB'|]. rewrite repeat_length.
    lazymatch type of HXC with u32arr _ _ ?a _ => replace (X + 4 * Z.of_nat (Z.to_nat n)) with a by klia end. assumption. }
  clear HXB' HXC.
  assert (LX' : Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs)) = Z.of_nat (length xs))
    by (rewrite app_length, repeat_length, length_skipn; klia).
  assert (FX' : same_from (Z.to_nat n) (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs) xs).
  { intros q Hq. rewrite nth_error_app2 by (rewrite repeat_length; klia). rewrite repeat_length, nth_error_skipn. f_equal. klia. }
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "MAIN-SIDE:" g end.
  clear HXC0 EY LP LXB8.
  destruct (Z_le_gt_dec blen 0) as [BL0 | BL0]; [|assert (BLP : 1 <= blen) by (clear - BL0; lia); assert (BPOS : 1 <= B) by (clear - NZB BL0; lia); clear BL0].
  (* [comment removed for export] *)
  all: lxr_pose; lx_spell; lx_pre; lx_run_tac (PLAN [0xa3cfc] [] 40%N); lx_tree.
  all: lx_same_mem; lx_gc; try clear OQH.
  - (* [comment removed for export] *)
    rewrite R0. lx_post; [> exact HX | clear - LX'; lia | apply same_from_skipn; [exact FX' | clear - LX'; lia] | .. ].
  - (* [comment removed for export] *)
    match goal with H4 : mem_inv asegs ?m2, H5 : stk asegs ?m2 lo (bv_unsigned sp + -48), H6 : HM _ _ _ h LB LF ?m2 |- _ =>
      pose proof (conj HX (conj LX' (conj FX' (conj MU (conj WM (conj H4 (conj H5 H6))))))) as DI end.
    eapply loop_walk with (h := h) (LB := LB) (LF := LF) (lx := Z.of_nat (length xs)) (lb := Z.of_nat (length bs)) (k := Z.to_nat blen) (i := 0);
      try eassumption; try reflexivity; try klia; try (f_equal; klia).
    all: first [ exact (unlock _ HB00) | idtac ].
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

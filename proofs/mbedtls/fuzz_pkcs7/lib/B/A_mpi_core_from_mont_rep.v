(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_core_montmul A_mpi_add_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0015f7ee7f770f67 1 1 64 2 0 1 61 1 3 2 1 62 1 63 64P00243f1ec7e13a5d 1 1 64 2 0 1 76 1 3 6 1 77 1 78 64P0053d906b9eb68e8 0 4 0 1 44 1 56 1 57 1P017b7f4e5386480e 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P029a4e32719d2b34 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P02afd50f566cb649 0 4 0 1 68 1 69 1 70 1P036e63174f2c5f7b 1 2 32 3 0 1 77 1 80 1 32 3 1 1 78 1 79 1 2 81 2 82 2P0383e4f67b5bade4 0 6 0 1 26 1 68 1 70 1 73 1 74 1P03df35f69075fb40 1 2 16 3 0 1 25 1 58 1 16 3 1 1 24 1 57 1 2 59 1 60 1P03f7289d452b5a57 0 6 0 1 46 1 47 1 48 1 56 1 57 1P04f3e30346662163 0 6 0 1 46 1 47 1 48 1 56 1 57 1P0548d2ef4e060561 0 6 0 1 46 1 47 1 48 1 56 1 57 1P05d53c7541b49079 0 6 0 1 46 1 47 1 48 1 56 1 57 1P05fa7f835b5ba155 0 3 0 1 37 1 67 1P06117021c0d4e630 0 4 0 1 68 1 69 1 70 1P06321f6378c95387 0 8 0 1 47 1 51 1 57 1 58 1 59 1 62 1 63 1P064b2d2127a4fa59 0 4 0 1 68 1 69 1 70 1P079dabcd0e255195 1 1 16 3 1 1 24 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P07af8fba7ad6f3d1 0 7 0 1 26 1 56 1 57 1 58 1 61 1 62 1P07df2617f61dc77e 1 2 32 3 0 1 78 1 79 1 32 3 1 1 77 1 80 1 2 81 2 82 2P0a53645dc2d56f54 0 4 0 1 44 1 56 1 57 1P0af3be4f230f39e9 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P0b21a984aa968413 0 5 0 1 46 1 48 1 56 1 57 1P0bba5902c4c7a5e3 1 1 16 3 1 1 24 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P0caffe1f99a7e173 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P0d267bdce7577693 1 2 32 3 1 1 77 1 80 1 32 8 36 1 41 1 60 1 67 1 68 1 69 1 78 1 79 1 2 81 1 82 1P0d62c434e5e51908 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P0e380bee9a89bc59 0 6 0 1 46 1 47 1 48 1 56 1 57 1P0e4417901f45c992 1 2 16 3 0 1 25 1 58 1 16 3 1 1 24 1 57 1 2 59 1 60 1P0eabbf1c64587e02 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P0f73356f02ed184c 1 1 16 2 1 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P12d6d6498d1e165a 0 5 0 1 46 1 48 1 56 1 57 1P133a747d23b4e18b 0 5 0 1 46 1 48 1 56 1 57 1P1492e3887b567d52 0 4 0 1 44 1 56 1 57 1P14a125ae975f563c 0 5 0 1 46 1 48 1 56 1 57 1P14ebc7e5ab47a5a5 0 5 0 1 46 1 48 1 56 1 57 1P15d82cf61fb8326d 1 1 16 3 0 1 78 1 79 1 8 41 1 60 1 67 1 68 1 69 1 77 1 80 1 81 16P1613b76f187c0446 0 4 0 1 68 1 69 1 70 1P1639c1615da36b0e 0 4 0 1 44 1 56 1 57 1P187e70e5916a95a4 0 3 0 1 37 1 55 1P19051257329b9af9 0 4 0 1 44 1 56 1 57 1P19612b5b900e1d27 1 1 16 3 0 1 78 1 79 1 8 41 1 60 1 67 1 68 1 69 1 77 1 80 1 81 16P19b4eb1df91f998a 0 4 0 1 25 1 73 1 74 1P1a58a259edb7e117 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P1ac1aacf8d2ec146 0 5 0 1 46 1 48 1 56 1 57 1P1ae19c8726fc4afe 0 4 0 1 25 1 73 1 74 1P1cc0e53c450981d3 0 4 0 1 44 1 56 1 57 1P1cd0cdee05a61cce 0 4 0 1 68 1 69 1 70 1P1d2f08f410e5e352 1 1 16 3 0 1 78 1 79 1 8 41 1 60 1 67 1 68 1 69 1 77 1 80 1 81 16P1e399979ffdbaa76 0 5 0 1 46 1 48 1 56 1 57 1P1e58d0a7f19505d2 0 4 0 1 44 1 56 1 57 1P1e70b3077715a385 0 3 0 1 37 1 67 1P1ee3a7b25f7c4417 1 2 32 3 0 1 77 1 80 1 32 8 36 1 41 1 60 1 67 1 68 1 69 1 78 1 79 1 2 81 1 82 1P1f359d508675162e 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P2079b619233cb6f2 0 3 0 1 37 1 67 1P21f5883b751c2b32 0 4 0 1 44 1 56 1 57 1P223449fea4255236 0 5 0 1 46 1 48 1 56 1 57 1P22edd8cd017b1199 0 3 0 1 37 1 67 1P23021718a89eebc9 0 6 0 1 46 1 47 1 48 1 56 1 57 1P2388a6b32a5fd43e 1 2 16 3 0 1 25 1 58 1 16 3 1 1 24 1 57 1 2 59 1 60 1P241011087c4b8669 0 6 0 1 35 1 66 1 68 1 76 1 77 1P246ea3864523bad6 0 4 0 1 68 1 69 1 70 1P247cf7bcc6d7cd83 1 2 32 3 0 1 76 1 79 1 32 8 35 1 40 1 59 1 66 1 67 1 68 1 77 1 78 1 2 80 1 81 1P24e72ac4ad063734 0 3 0 1 37 1 67 1P2544b625b4e75d55 1 1 16 3 0 1 78 1 79 1 8 41 1 60 1 67 1 68 1 69 1 77 1 80 1 81 16P26fb30a5c6a8fd6e 1 1 16 2 1 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P282bee7e55a3d83b 0 4 0 1 44 1 56 1 57 1P28bef343c0da87d8 0 4 0 1 56 1 57 1 58 1P29898427daf73273 0 3 0 1 29 1 38 1P299c97cf14f3cc2d 1 1 16 2 1 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P29c5d57904319dd1 0 3 0 1 39 1 45 1P2a0a66ea910d3c63 0 6 0 1 25 1 37 1 55 1 61 1 62 1P2a990ed5e687d1d5 0 4 0 1 68 1 69 1 70 1P2aa7d632109464fc 0 7 0 1 35 1 66 1 67 1 68 1 76 1 77 1P2ac0631ca176d13a 1 1 16 3 1 1 24 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P2af35737c149bbe9 0 5 0 1 46 1 48 1 56 1 57 1P2b9cd138d989a4e3 1 1 16 3 0 1 77 1 78 1 8 40 1 59 1 66 1 67 1 68 1 76 1 79 1 80 16P2ccf691297ef3cc6 0 3 0 1 37 1 67 1P2d0fd94e9252dbd0 1 1 16 2 30 1 56 1 3 0 1 57 1 58 16P2d4dd0fb9d541d22 0 4 0 1 44 1 56 1 57 1P2e05bc8f7e98bda7 0 3 0 1 37 1 67 1P2e85125bfd561b11 0 4 0 1 68 1 69 1 70 1P2f29596fc9416038 0 5 0 1 46 1 48 1 56 1 57 1P2f52b3183d5aad1a 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P2f746c03968b9537 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P2f7c2c2ac4504045 1 2 32 3 0 1 77 1 80 1 32 3 1 1 78 1 79 1 2 81 2 82 2P2fdf9b0a9ddc604f 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P300a27d56e54f766 1 1 64 2 47 1 62 1 3 0 1 61 1 63 64P300ea1eef53b242f 0 4 0 1 68 1 69 1 70 1P302e624d50d18310 1 2 16 3 0 1 25 1 58 1 16 3 1 1 24 1 57 1 2 59 1 60 1P30bfbb36751b0ef1 1 2 32 3 0 1 62 1 65 1 32 3 1 1 63 1 64 1 2 66 2 67 2P31243ef1317eaad2 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P31c2e3aa2eb59bd1 1 2 16 3 0 1 25 1 58 1 16 3 1 1 24 1 57 1 2 59 1 60 1P31fc6d3e76fdfcaa 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P34b6d9138bef4c13 1 1 16 3 0 1 78 1 79 1 4 55 1 77 1 80 1 81 16P34fc93352cfe33b8 0 6 0 1 46 1 47 1 48 1 56 1 57 1P3512f0fbcb178ced 1 1 16 2 1 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P35757c8c49616905 0 4 0 1 68 1 69 1 70 1P3584e2351723ce61 0 6 0 1 51 1 54 1 64 1 76 1 77 1P35ce5db5e5f6be73 1 1 16 3 0 1 77 1 78 1 4 54 1 76 1 79 1 80 16P3604a9358dc70cf6 1 1 16 3 1 1 24 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P3633e8a20e4ddb38 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P3639b31eca45e280 0 3 0 1 37 1 67 1P366234502587c010 1 2 16 3 0 1 25 1 58 1 16 3 1 1 24 1 57 1 2 59 1 60 1P369378293680a30f 0 6 0 1 46 1 47 1 48 1 56 1 57 1P372342a4dc1b568b 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P373dfb23c862f8e0 0 5 0 1 66 1 68 1 76 1 77 1P37c125c5d98d3ab7 1 1 16 2 1 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P37ef3efb6a78e4fe 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P3858ab2e77ab09d5 1 2 32 3 0 1 77 1 80 1 32 3 1 1 78 1 79 1 2 81 2 82 2P3ac1c680d306f531 0 4 0 1 25 1 73 1 74 1P3b50601510fbc732 1 1 64 2 1 1 61 1 3 0 1 62 1 63 64P3bf4af0b9a52e620 1 1 64 2 5 1 76 1 3 0 1 77 1 78 64P3ce419f2c444c440 1 1 16 4 1 1 26 1 35 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P3d255fa8b23d3099 0 4 0 1 44 1 56 1 57 1P3d7ff8a702361443 0 5 0 1 46 1 48 1 56 1 57 1P3e5ae1d4de26ef79 0 4 0 1 25 1 73 1 74 1P3e9a4dc36d6c27d0 0 6 0 1 46 1 47 1 48 1 56 1 57 1P3ebe5c24b8b0c480 0 3 0 1 37 1 67 1P3ec856493adc4d40 1 1 16 3 1 1 24 1 57 1 7 38 1 40 1 47 1 48 1 49 1 58 1 59 16P3eeef3512d9ee8a5 1 2 32 3 0 1 76 1 79 1 32 8 35 1 40 1 59 1 66 1 67 1 68 1 77 1 78 1 2 80 1 81 1P3f0a9bf92190a752 0 6 0 1 46 1 47 1 48 1 56 1 57 1P3fb6d5a76d2323d8 0 3 0 1 37 1 67 1P3fc354b56a324cff 0 6 0 1 46 1 47 1 48 1 56 1 57 1P3fdd0f3a9f6aa220 1 1 16 2 0 1 56 1 3 4 1 57 1 58 16N001c645d5fbdee5aN03acba273a49249fN0617e0c2642060d9N068a2378aefbea8bN077868591c4ea71dN083e550428dbe063N091a353851e56821N09304c0d0e311a54N0940968d96550761N0a605b3073e2023aN0a8c0b0204f27c08N0b619957fe391766N0bf50fc344b9f02cN0c622d754c6a32eaN0f3eb97c2aeeccdeN10c590398ceffc41N11cbd7d664b74d5fN13a4e4b42d65e0faN146301e9241e6a86N168c6f7430cccf6fN176755e4731c9ab9N17806db133dd2103N1bf2a36d61fcedb2N1d8763afc49fcafcN1eba837fb05c58b3N1f64f4e30229e39fN2328504fa7acdd78N232fc744a8b5a21eN246706d7e5caf5bfN24d23fb67e2c0783N271587502a2d1b0fN27cae294d8c9c8b8N29f257987717d667N2ad3979123ed6102N2c9d1e4dfb295e26N2d23993a48c04baeN2ef61eeb871c9e69N3090fdd46055bda1N31366ff0a97e25caN31ff760fcbe9e673N34f9eaaa6990bfd9N36a4ff82d37104fcN36c9b80c8ccea35fN3a10f6441af5eab8N3b04b84d45e5a9deN3c2ba0dd61c2b993N3c34a1ec34b0005aN3fdaca78d0b5525e"%lxh.
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
Ltac2 gd_tbl_A_mpi_core_from_mont_rep () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_FROM_MONT_REP_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_from_mont_rep_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.A_MPI_CORE_MONTMUL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "WalkF.Call.S1P"; "A_MPI_CORE_FROM_MONT_REP"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "WalkF.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_int.A_UAR_GOT_M"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "A_SMALLOC_0_F"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.mpi_core_montmul_stmtA"; "mpi_core_from_mont_rep_stmtA"].


Definition A_MPI_CORE_FROM_MONT_REP : Z := 0xa66cc.   (* [comment removed for export] *)
Definition A_SMALLOC_0_F : Z := 0x52ef8.               (* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
Definition MPI_CORE_FROM_MONT_REP_STACK_A : Z := 400.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L17488201933.17000004S2ws". (* [comment removed for export] *)
Lemma presA_u32arr : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Psegs,(0.$1.)PR,$2.PLB,(0.$3.)PLF,(0.$3.)PSP,$4.PSSP,$4.PTOP,$4.PW,(0.$5.)Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))PA,$4.Pws,(0.(6.&40.))P,(8.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(9.R=.R5.R3.R2.)P,(:.(;.R=.)(<.$3.R<.(=.R;.))R:.R4.(>.+4.(?.(10.(6.&40.)R3.))))P,(11.R8.R5.(>.+4.(?.(10.(6.&40.)R4.))))(9.R10.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs R LB LF SP SSP TOP W m m' A ws HP [HB HW] CR DJ. split.
  - eapply (presA_bytes_at segs R); [exact HP| exact HB| rewrite u32s_length; replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia; exact CR
                                    | rewrite u32s_length; replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia; exact DJ].
  - eapply heap_presx_wr_at; [exact (presA_presx segs R _ _ _ _ _ _ _ _ HP)| exact HW| exact CR| exact DJ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition mpi_core_from_mont_rep_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X an T : Z) (xs ts : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Lms',$12.(13.(6.&40.)Lt0,(6.&40.)(13.(6.&40.)Lt1,(6.&40.)(13.(6.&40.)Lt2,(6.&40.)(13.(6.&40.)La0,(6.&40.)(13.(6.&40.)La1,(6.&40.)(13.(6.&40.)La2,(6.&40.)(13.(6.&40.)La3,(6.&40.)(13.(6.&40.)La4,(6.&40.)(13.(6.&40.)La5,(6.&40.)(13.(6.&40.)La6,(6.&40.)(13.(6.&40.)La7,(6.&40.)(13.(6.&40.)Lt3,(6.&40.)(13.(6.&40.)Lt4,(6.&40.)(13.(6.&40.)Lt5,(6.&40.)(13.(6.&40.)Lt6,(6.&40.)(13.P,(6.&40.)(7.(6.&8.))Lm',P,(6.&40.)(7.(6.&8.))(13.(14.O1?.O1>.O1=.)Lh',(14.O1?.O1>.O1=.)(13.(0.(6.&40.))Lxs',(0.(6.&40.))(13.(0.(6.&40.))Lts',(0.(6.&40.))(15.(16.$12.R14.(17.(18.O19.O18.O17.O16.R13.R12.R11.O15.O14.R10.R?.R>.R=.R<.R;.R:.R9.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R8.R7.R6.R5.)O9.(19.O19.)O8.(1:.(6.&40.))R4.(1;.O1?.)))(15.(1<.O1?.R4.)(15.(1=.O1?.R4.O2.(1>.&40.O18.))(15.(8.O1?.O1>.O1;.O1:.(1>.&40.O18.)(1?.O1>.)(20.O1?.O1>.O1=.O1<.)(21.(22.$4.$4.)(23.$4.$4.O7.(24.O7.(>.+4.O6.)))(21.(22.$4.$4.)(23.$4.$4.O5.(24.O5.(>.+4.(24.(>.+2.O6.)+1.))))(25.(22.$4.$4.))))O1.R4.)(15.(9.O1?.R4.O7.R2.)(15.(16.$26.(10.(6.&40.)R2.)(10.(6.&40.)O4.))(15.(16.(0.(6.&40.))(27.(6.&40.)(28.O6.)R2.)(27.(6.&40.)(28.O6.)O4.))(15.(9.O1?.R4.O5.R1.)(15.(16.$26.(10.(6.&40.)R1.)(10.(6.&40.)O3.))(15.(16.(0.(6.&40.))(27.(6.&40.)(28.(24.(>.+2.O6.)+1.))R1.)(27.(6.&40.)(28.(24.(>.+2.O6.)+1.))O3.))(15.(29.O1?.O1>.O1=.R3.O1;.O1:.R4.)(15.(16.P,$4.Sp(2:.O1?.O1>.O1=.R3.)(2:.O1?.O1>.O1=.O1<.))(15.(16.$4.(2;.O1?.O1>.O1=.R3.)(2;.O1?.O1>.O1=.O1<.))(15.(16.$4.(20.O1?.O1>.O1=.R3.)(20.O1?.O1>.O1=.O1<.))(15.(16.$4.(2<.O1?.O1>.O1=.R3.)(2<.O1?.O1>.O1=.O1<.))(15.(16.$4.(2=.O1?.O1>.O1=.R3.)(2=.O1?.O1>.O1=.O1<.))(15.(16.$4.(2>.O1?.O1>.O1=.R3.)(2>.O1?.O1>.O1=.O1<.))Pmo,$2?.(30.(31.O1?.O1>.O1=.R4.R1.)(31.O1?.O1>.O1=.O1<.R1.))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_from_mont_rep_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Ph,(14.O4.O3.O2.)PLB,(0.$3.)PLF,(0.$3.)Pra,(6.&40.)Psp,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa0,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)PF,(32.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(7.(6.&8.))PX,$4.PA,$4.PN,$4.Pan,$4.PT,$4.Plo,$4.Pxs,(0.(6.&40.))Pys,(0.(6.&40.))Pns,(0.(6.&40.))Pts,(0.(6.&40.))P,(29.O4.O3.O2.R2?.R2>.R2=.R;.)P,(33.(10.$3.R2>.)#200.)P,(9.O4.R=.R<.R6.)P,(34.O4.R>.R<.(35.R6.))P,(34.O4.R?.R<.(35.R6.))P,(9.O4.R10.R;.R6.)P,(15.(36.+1.R=.)(36.R=.+1387.))P,(36.R>.(?.(10.(6.&40.)R;.)))P,(36.R?.(?.(10.(6.&40.)R;.)))P,(36.R10.(?.(10.(6.&40.)R;.)))P,(36.(24.(>.+2.R11.)+1.)(?.(10.(6.&40.)R;.)))P,(37.(36.(24.R15.(>.+4.(?.(10.(6.&40.)R?.))))R11.)(36.(24.R11.(>.+4.(?.(10.(6.&40.)R<.))))R15.))P,(37.(36.(24.R15.(>.+4.(?.(10.(6.&40.)R?.))))R12.)(36.(24.R12.(>.+4.(?.(10.(6.&40.)R=.))))R15.))P,(37.(36.(24.R15.(>.+4.(?.(10.(6.&40.)R?.))))R13.)(36.(24.R13.(>.+4.(?.(10.(6.&40.)R>.))))R15.))P,(37.(36.(24.R16.(>.+4.(?.(10.(6.&40.)R10.))))R18.)(36.(24.R18.(>.+4.(?.(10.(6.&40.)R12.))))R16.))P,(16.$4.(38.R19.+4.)=)P,(16.$4.(38.R19.+4.)=)P,(16.$4.(38.R19.+4.)=)P,(16.$4.(38.R18.+4.)=)P,(39.=R1=.)P,(39.=R1=.)P,(39.=R1=.)P,(39.=R1<.)P,(39.(24.R21.(>.+4.(?.(10.(6.&40.)R1;.))))(3:.+2.+40.))P,(39.(24.R21.(>.+4.(?.(10.(6.&40.)R1;.))))(3:.+2.+40.))P,(39.(24.R21.(>.+4.(?.(10.(6.&40.)R1;.))))(3:.+2.+40.))P,(39.(24.R20.(>.+4.(?.(10.(6.&40.)R1;.))))(3:.+2.+40.))P,(1=.O4.R26.R20.(1>.&40.R46.))P,(36.(1?.O3.)R21.)P,(36.R22.(3;.(3;.(1>.&40.R48.)$3<.)(3=.O3.)))P,(36.R23.(3;.(3;.(1>.&40.R49.)+70.)(3>.O3.)))P,(36.(1>.&40.R4:.)(2;.O4.O3.O2.R4>.))P,(16.$4.(38.(1>.&40.R4;.)+10.)=)P,(16.(6.&40.)R4:.(3?.&40.(40.O3.)))P,(37.(36.(24.R2<.(>.+4.(?.(10.(6.&40.)R26.))))R27.)(36.(1>.&40.R4=.)R2<.))P,(37.(36.(24.R2<.(>.+4.(?.(10.(6.&40.)R26.))))R28.)(36.(1>.&40.R4>.)R2<.))P,(37.(36.(24.R2<.(>.+4.(?.(10.(6.&40.)R26.))))R29.)(36.(1>.&40.R4?.)R2<.))P,(37.(36.(24.R2;.(>.+4.(?.(10.(6.&40.)R26.))))R2:.)(36.(1>.&40.R50.)R2;.))P,(41.(;.O3.)(<.$3.R54.(=.R53.))(1?.O3.)(2;.O4.O3.O2.R55.)R30.(>.+4.R2=.))P,(41.(;.O3.)(<.$3.R55.(=.R54.))(1?.O3.)(2;.O4.O3.O2.R56.)R2=.(>.+4.(24.(>.+2.R2>.)+1.)))P,(:.(;.O3.)(<.$3.R56.(=.R55.))R2=.R32.(>.+4.(?.(10.(6.&40.)R2<.))))P,(:.(;.O3.)(<.$3.R57.(=.R56.))R2>.R32.(>.+4.(?.(10.(6.&40.)R2<.))))P,(37.(:.(;.O3.)(<.$3.R58.(=.R57.))R2?.R32.(>.+4.(?.(10.(6.&40.)R2<.))))(15.Pi,$4.P,(15.(36.=R1.)(39.R1.(>.+4.(?.(10.(6.&40.)R2=.)))))(16.$42.(43.O4.(44.(24.R34.R2.)))$45.)(16.$42.(46.R32.(>.+4.(?.(10.(6.&40.)R2<.))))$45.)))P,(:.(;.O3.)(<.$3.R59.(=.R58.))R30.R31.(>.+4.(?.(10.(6.&40.)R2<.))))P,(1<.O4.R37.)P,(16.$4.(38.(1>.&40.R59.)+2.)=)P,(47.O4.(48.O3.)(2:.O4.O3.O2.R5=.)R39.R38.(>.+4.R35.))P,(47.O4.(48.O3.)(2:.O4.O3.O2.R5>.)R3:.R38.(>.+4.R36.))P,(47.O4.(48.O3.)(2:.O4.O3.O2.R5?.)R3;.R38.(>.+4.R37.))P,(47.O4.(48.O3.)(2:.O4.O3.O2.R60.)R3<.R37.(>.+4.(24.(>.+2.R38.)+1.)))P,(16.(6.&40.)R55.(3?.&40.R3<.))P,(16.(6.&40.)R55.(3?.&40.R3<.))P,(16.(6.&40.)R55.(3?.&40.R3<.))P,(16.(6.&40.)R55.(3?.&40.R3<.))P,(16.(6.&40.)R54.(3?.&40.R3<.))(49.O4.(48.O3.)(2:.O4.O3.O2.R66.)(4:.O4.O3.O2.R66.R65.R64.R63.R62.R61.R60.R5<.R5;.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R44.R43.R41.R3>.R3=.R3;.R38.R3<.R42.)(17.(18.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.)R44.(3?.&40.O1.)R43.(1:.(6.&40.))R42.(1;.O4.)))")
(* [comment removed for export] *).

Section WalkF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_M.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0_F.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_amem R.
  Hypothesis MM : mpi_core_montmul_stmtA asegs R HIA A_MPI_CORE_MONTMUL.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A N an T lo : Z) (mmw : word).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 400 - arl_need_amem R.
  Hypothesis SLOS : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_M in UARG; unfold A_SMALLOC_0_F in SM0;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 4);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Lms,$12.(13.$4.LFB,$4.(13.$4.Lsp1,$4.(13.(14.$4;.VR,VHIA,)Lh1,(14.$4;.VR,VHIA,)(13.P,(6.&40.)(7.(6.&8.))Lm1,P,(6.&40.)(7.(6.&8.))(13.(6.&40.)Lt0,(6.&40.)(13.(6.&40.)Lt1,(6.&40.)(13.(6.&40.)Lt2,(6.&40.)(13.(6.&40.)Lt3,(6.&40.)(13.(6.&40.)Lt4,(6.&40.)(13.(6.&40.)Lt5,(6.&40.)(13.(6.&40.)Lt6,(6.&40.)(13.(6.&40.)Lw0,(6.&40.)(13.(6.&40.)Lw1,(6.&40.)(13.(6.&40.)Lw2,(6.&40.)(15.(16.$12.R?.(17.(18.(3?.&40.+:6804.)(3?.&40.R=.)Vgp,Vtp,R:.R9.R8.Vsp,(3?.&40.R=.)(3?.&40.VX,)(3?.&40.VA,)(3?.&40.(24.R>.+20.))(3?.&40.+1.)(3?.&40.VN,)(3?.&40.Van,)Vmmw,(3?.&40.VT,)(3?.&40.R>.)(3?.&40.VT,)Vmmw,(3?.&40.Van,)(3?.&40.VN,)(3?.&40.(24.(4<.R>.+3.)(4=.(48.VR,))))(3?.&40.R>.)Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(3?.&40.$4>.)Vfc,(1:.(6.&40.))R;.(1;.$4;.)))(15.(15.(36.(3;.(1>.&40.Vsp,)+70.)R=.)(36.R=.(3;.(1>.&40.Vsp,)+60.)))(15.(16.$4.(38.R=.+20.)=)(15.(29.$4;.VR,VHIA,R<.VLB,(21.(22.$4.$4.)(23.$4.$4.R>.+40.)VLF,)R;.)(15.(16.P,$4.Sp(2:.$4;.VR,VHIA,R<.)(2:.$4;.VR,VHIA,Vh,))(15.(16.$4.(2;.$4;.VR,VHIA,R<.)(2;.$4;.VR,VHIA,Vh,))(15.(16.$4.(20.$4;.VR,VHIA,R<.)(20.$4;.VR,VHIA,Vh,))(15.(16.$4.(2<.$4;.VR,VHIA,R<.)(2<.$4;.VR,VHIA,Vh,))(15.(16.$4.(2=.$4;.VR,VHIA,R<.)(2=.$4;.VR,VHIA,Vh,))(15.(16.$4.(2>.$4;.VR,VHIA,R<.)(2>.$4;.VR,VHIA,Vh,))(15.Pmo,$2?.(30.(31.$4;.VR,VHIA,R=.R1.)(31.$4;.VR,VHIA,Vh,R1.))(15.(16.$4.(38.R>.+40.)=)(15.(4?.VR,VLB,VLF,R>.+40.)(15.(50.$4;.R;.R>.(21.$51.(52.R3.)(21.$51.(52.R2.)(21.$51.(52.R1.)(25.$51.)))))(15.(50.$4;.R;.(24.R>.+20.)(21.$51.(53.(3?.&40.+1.))(25.$51.)))(15.(50.$4;.R;.(24.(4<.R>.+3.)(4=.(48.VR,)))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+4.))(21.$51.(54.(3?.&8.+?3.))(21.$51.(54.(3?.&8.+?3.))(21.$51.(54.(3?.&8.+?3.))(25.$51.))))))))))(15.(50.$4;.R;.(24.(1>.&40.Vsp,)-50.)(21.$51.(52.Vs8,)(21.$51.(52.Vs7,)(21.$51.(52.Vs6,)(21.$51.(52.Vs5,)(21.$51.(52.Vs4,)(21.$51.(52.Vs3,)(21.$51.(52.Vs2,)(21.$51.(52.Vs1,)(21.$51.(52.Vs0,)(21.$51.(52.Vra,)(25.$51.))))))))))))(15.(50.$4;.R;.(24.R=.+8.)(21.$51.(52.(3?.&40.R>.))(25.$51.)))(15.(1=.$4;.R;.R=.(24.R=.+8.))(15.(1=.$4;.R;.(24.R=.+10.)(24.(1>.&40.Vsp,)-50.))(15.(1=.$4;.R;.Vlo,R=.)(15.(1<.$4;.R;.)(55.$4;.VR,VHIA,Vh,VLB,VLF,(1>.&40.Vsp,)(1?.VR,)(25.$5.)Vm,R;.)))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 MM.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0180@D18607476203.109D2457697676.138 D32458983511.138D32604263317.139D3375410824.137 D45716866873.137D50132923712.138D50254960491.110D558665111.79   D58077997354.110D62009822325.79 D62011770190.139D68407129291.137D6911780558.137 L17605293680.124L1832968857.10  L19546883925.124L19685319514.133L19980016842.10 L21101670104.1  L29738741675.1  L31168734363.119L33473079733.80 L33483560980.11 L33485826452.1  L36180999398.74 L3876079316.7   L38903380038.3  L43055154860.72 L45363093875.142L47230721790.119L48117620902.120L48117620911.69 L49130057368.10 L55351494680.11 L567271841.0    L56841705562.78 L57355539152.120L58077947190.134L58790154276.10 L59308634497.12 L62018535662.1  L64787780871.1  L67412691327.1  L67922604617.0  L6912107244.119 L7040749983.79  L9356559645.11  Q10533598597.81 Q10592386206.143Q1530342990.110 Q23218748859.143Q23937998252.81 Q31158247845.142Q31168734363.144Q32440833928.142Q35653441506.67 Q40271359350.110Q47241206720.81 Q48117620904.143Q48132302231.142Q56531220660.143Q59310664043.142Q59310664043.81 Q59321150548.143Q60109315147.67 Q6192914196.108 Q62012212072.110Q62022254708.81 Q6897428434.142 Q6912107244.144 Q9356560156.91  00000100200H00g00h01>01T01U01h02?02L02d02e03;03[03\04<04R04j04o05305>05?05@05A05L05f06206P06k07907[08=08>08N08O09609709Q09g0:10:40:80:=0:>0:I0:d0;O0;\0;g0<:0<E0<a0<l0=70=80=W0=g0>50>W0?90?:0?;0?<0?=0?N0?Z0?d0?n0@90@D0@XFFS2LF2sp3LFB3sp13H152FBS1R3HIA2LF2sp3LFB3sp13H152h12FBFS2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H152FBFS1R3HIA1h2LF2sp3LFBS2LF2sp3LFB3sp13H133H15S1R2LF2sp3LFBS1R2LF2sp3LFB3sp13H152FBFS2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3SPR3sp13H152FB2F02F8SS2LF2sp3LFB3SPR3sp13H152FB2F02F8S2LF2sp3LFB3sp13H152FBS1R3HIA1h2sp3TOP3sp13SP1S3sp1S2FBS2LF3LFB2FBFFFS2LF2sp3LFBS1R3NS12sp2lo4SLOS3sp13SP1S2sp3sp13SP1S1R5NEEDR2LF2sp2lo3SLO3LFB3SPRS2LF2sp3LFB3sp13H152FB1c2HcS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOSS1R3ACV2FB2F02F1SS2LF2sp3SPA3LFB3SPR3sp13H113H123H133H15FS2LF2sp3LFB3sp13H133H152FBS1R2sp2lo4SLOS3sp13SP1S2FB2F02KbS1RS2spS3sp1SS2LF3LFB2FBS2LF2sp3LFB3SPR3sp13H113H15S1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S1R2LF2sp3LFBS2LF3LFB2FBS2LF2sp3LFB3sp13H13S2LF3LFB2FBS1R3HIA1h2LF2sp3TOP3LFB4HTOPS2LF3LFB2FBS2LF3LFB2FBFS1R3HIA1h2LF2sp2lo3TOP3LFB4HTOPS1R3HIA1h2LF3LFBS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOFFFFS1R2LF2lo3LOS3LFBS2LF3LFB3sp1S1R2LF3LFBS1R2LF3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB3sp13H143H15". (* [comment removed for export] *)
  #[using="LFB TPV SPA TOP SLOS SLO LOS NEEDR NS1 SM0 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)P,(29.$4;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(1=.$4;.Vm,Vlo,(1>.&40.Vsp,))P,(1<.$4;.Vm,)(49.$4;.(48.VR,)(2:.$4;.VR,VHIA,Vh,)$56.(17.(18.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(3?.&40.VX,)(3?.&40.VA,)(3?.&40.VN,)(3?.&40.Van,)Vmmw,(3?.&40.VT,)R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(3?.&40.$57.)Vfc,(1:.(6.&40.))Vm,(1;.$4;.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST MI.
  unfold A_MPI_CORE_FROM_MONT_REP.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  carve_frame 96%nat ST.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 137%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(first [ clear - SP1 SLOS NS1; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 339704) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLOS SP1 TOP NS1; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _).
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 0) with 64 in *. change (8 * 2 ^ 0) with 8 in FSH. change (Z.to_nat 64) with 64%nat in FRM. change (Z.to_nat 8) with 8%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS. change (64 - 40) with 24 in IND.
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -96 + 16) with (bv_unsigned sp + -80) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa STx (bv_unsigned sp + -80); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 16) (bv_unsigned sp + -80) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 16) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
      replace (sp1 + 16 - Z.of_nat 8) with (sp1 + 8) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
      cb8_to_c8 SLOT (@nil cell).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [8; 8; 8; 8; 4; 28]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat LMB FREST.
      lazymatch type of LMB with rw_cells _ _ ?a _ => replace a with (FB + 32) in LMB by (clear; lia) end.
      clear FLNK FREST.
      cb8_to_c8 FHD (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0xa54a0] [] 137%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end).
  try (match goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb _) _ |- _ => rename H into FSHX end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      do 7 eexists. do 3 eexists.
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [eassumption|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact STlo|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|].
      exact PRES.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Lms,$12.(13.P,(6.&40.)(7.(6.&8.))Lm',P,(6.&40.)(7.(6.&8.))(13.(14.$4;.VR,VHIA,)Lh4,(14.$4;.VR,VHIA,)(13.(6.&40.)Lt0,(6.&40.)(13.(6.&40.)Lt1,(6.&40.)(13.(6.&40.)Lt2,(6.&40.)(13.(6.&40.)La0,(6.&40.)(13.(6.&40.)La1,(6.&40.)(13.(6.&40.)La2,(6.&40.)(13.(6.&40.)La3,(6.&40.)(13.(6.&40.)La4,(6.&40.)(13.(6.&40.)La5,(6.&40.)(13.(6.&40.)La6,(6.&40.)(13.(6.&40.)La7,(6.&40.)(13.(6.&40.)Lt3,(6.&40.)(13.(6.&40.)Lt4,(6.&40.)(13.(6.&40.)Lt5,(6.&40.)(13.(6.&40.)Lt6,(6.&40.)(15.(16.$12.R12.(17.(18.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,R<.R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(19.Vra,)Vfc,(1:.(6.&40.))R11.(1;.$4;.)))(15.(1<.$4;.R11.)(15.(1=.$4;.R11.Vlo,(1>.&40.Vsp,))(15.(55.$4;.VR,VHIA,O7.O6.VLF,(1>.&40.Vsp,)(1?.VR,)O2.O4.R11.)(15.(55.$4;.VR,VHIA,O7.O5.VLF,(1>.&40.Vsp,)(1?.VR,)O1.O3.R11.)(15.(16.P,$4.Sp(2:.$4;.VR,VHIA,R10.)(2:.$4;.VR,VHIA,O7.))(15.(16.$4.(2;.$4;.VR,VHIA,R10.)(2;.$4;.VR,VHIA,O7.))(15.(16.$4.(20.$4;.VR,VHIA,R10.)(20.$4;.VR,VHIA,O7.))(15.(16.$4.(2<.$4;.VR,VHIA,R10.)(2<.$4;.VR,VHIA,O7.))(15.(16.$4.(2=.$4;.VR,VHIA,R10.)(2=.$4;.VR,VHIA,O7.))(15.(16.$4.(2>.$4;.VR,VHIA,R10.)(2>.$4;.VR,VHIA,O7.))(15.Pmo,$2?.(30.(31.$4;.VR,VHIA,R11.R1.)(31.$4;.VR,VHIA,O7.R1.))(29.$4;.VR,VHIA,R10.O5.VLF,R11.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 SLOS; try lx_pin1 mmw; try lx_pin1 T; try lx_pin1 an; try lx_pin1 N; try lx_pin1 A; try lx_pin1 X; try lx_pin1 m; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 LB; try lx_pin1 MM; try lx_pin1 NS1; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@D2459793318.115 D32452690557.115D3385958441.114 D43016287773.116D45702252952.114D62011770188.116D64997949699.115D68409162346.114D6897035375.114 L14337378910.154L16578761643.1  L17605293682.99 L17605293695.103L19546883927.99 L19546883930.103L21189212268.149L21224591641.144L31168734356.100L31168734361.96 L35559589539.1  L35655538631.9  L39332637397.0  L39972639317.0  L41375007627.155L42330892138.152L42411609006.0  L45363093875.119L47230721777.100L47230721788.96 L48117620903.101L48117620904.97 L50790580594.6  L55715474836.2  L60098763854.3  L60543874632.6  L62018535662.1  L62234724268.153L66730930849.8  L67922604617.0  L6912107235.100 L6912107246.96  L9356559676.11  P55705235216.149Q10592386204.120Q10592386207.124Q14681873509.121Q14681873512.125Q22358563588.123Q23218748857.120Q23218748858.124Q30147450662.121Q31158247845.119Q31158247869.123Q31168734356.125Q31168734361.121Q31314676345.119Q33433749386.147Q34796740410.124Q4125667684.146 Q4279611329.148 Q4590099355.147 Q48117620905.124Q48117620906.120Q48132302223.123Q48132302231.119Q5935758158.148 Q59668625896.125Q60382659730.125Q60382659743.121Q64133651577.147Q67397950268.120Q6897428426.123 Q6897428434.119 Q6912107235.125 Q6912107246.121 Q7917062807.125 Q7917062810.121 00000100@00A00Y00h01901H01I01X02E02I02c03=03R03g04604J04U04`04d05=05>05?05j06S06T06h07607D07f08H08_08`08j09A09D0:10:P0:Q0:\0:g0;R0;S0;^0;i0;j0;k0;l0<70<B0<C0<N0<Y0<d0<o0=00=@0=A0=N0=[0=k0>M0>o0?Q0@30@@0@A0@B0@C0@P0@Q0@\0@g0A20A=0AQ0AeFS2LF3LFB2FB3sp1FS1R3HIA2LF3LFB2h32FB3sp1S2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1S2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP14SP1R2F0S2FBS2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp1S2LF3LFB2FB3sp11p2PBS2LF3LFB2FBS2LF3LFB2FBS2spS1R3HIA1h2sp2lo3TOP5HTOP3SSS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP12F02H7S1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14SP1R2F0SS2LF3LFB2FB3sp11c2HcS1R2LF3LFB3ALOS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2sp2lo3LOS3SLOFS1R2lo3LOSS1R5NEEDR2sp2lo3LOS3SLOS1RS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP14SP1R2F0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP1SS2LF3LFB2FBS2LF3LFB2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS2LF3LFB2FBS2LF3LFB2FBFFFS2LF3LFB2FBS2LF3LFB2FBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS2LF3LFB2FB1p2PBFS2LF3LFB1p2PBS2LF3LFB1p2PBS2LF3LFB2FB1p2PBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS2LF3LFB1p2PBFFFS2LF3LFB1p2PBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1". (* [comment removed for export] *)
  #[using="LFB TOP SLO LOS NEEDR IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Ph3,(14.$4;.VR,VHIA,)PLBa,(0.$3.)PLBb,(0.$3.)Pm0,P,(6.&40.)(7.(6.&8.))Pm2x,P,(6.&40.)(7.(6.&8.))Pmm,P,(6.&40.)(7.(6.&8.))PWA,(0.$5.)PWB,(0.$5.)PFB,$4.Psp1,$4.Pxra,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa0,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Ps3v,(6.&40.)Ps4v,(6.&40.)Ps5v,(6.&40.)Ps6v,(6.&40.)Pw0,(6.&40.)Pw1,(6.&40.)Pw2,(6.&40.)P,(29.$4;.VR,VHIA,R21.R1?.(21.(22.$4.$4.)(23.$4.$4.R19.+40.)VLF,)R1<.)P,Px,$4.P,(2:.$4;.VR,VHIA,Vh,R1.)(2:.$4;.VR,VHIA,R24.R2.)P,(16.$4.(2;.$4;.VR,VHIA,R23.)(2;.$4;.VR,VHIA,Vh,))P,(16.$4.(20.$4;.VR,VHIA,R24.)(20.$4;.VR,VHIA,Vh,))P,(15.(36.(3;.(1>.&40.Vsp,)+70.)R1<.)(36.R1<.(3;.(1>.&40.Vsp,)+60.)))P,(16.$4.(38.R1=.+20.)=)P,(16.$4.(38.R1?.+40.)=)P,(4?.VR,R27.VLF,R20.+40.)P,(4?.VR,R27.VLF,R21.+40.)P,(58.(2:.$4;.VR,VHIA,Vh,)R22.+40.)P,PB,$4.Pj,$4.P,(59.(22.$4.$4.)(23.$4.$4.R2.R1.)VLF,)(37.(36.(24.R26.+40.)R3.)(36.(24.R3.R2.)R26.))P,Pb',$3.P,(59.$3.R1.R2<.)(59.$3.R2.R2<.)P,(50.$4;.R28.R25.(21.$51.(52.R?.)(21.$51.(52.R>.)(21.$51.(52.R=.)(25.$51.)))))P,(50.$4;.R29.(24.(4<.R26.+3.)(4=.(48.VR,)))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+?1.))(21.$51.(54.(3?.&8.+4.))(21.$51.(54.(3?.&8.+?3.))(21.$51.(54.(3?.&8.+?3.))(21.$51.(54.(3?.&8.+?3.))(25.$51.))))))))))P,(50.$4;.R2:.(24.(1>.&40.Vsp,)-50.)(21.$51.(52.Vs8,)(21.$51.(52.Vs7,)(21.$51.(52.Vs6,)(21.$51.(52.Vs5,)(21.$51.(52.Vs4,)(21.$51.(52.Vs3,)(21.$51.(52.Vs2,)(21.$51.(52.Vs1,)(21.$51.(52.Vs0,)(21.$51.(52.Vra,)(25.$51.))))))))))))P,(50.$4;.R2;.(24.R27.+8.)(21.$51.(52.(3?.&40.R28.))(25.$51.)))P,(1=.$4;.R2<.R28.(24.R28.+8.))P,(1=.$4;.R2=.(24.R29.+10.)(24.(1>.&40.Vsp,)-50.))P,(1=.$4;.R2>.Vlo,R2:.)P,(1<.$4;.R2?.)P,(55.$4;.VR,VHIA,R35.R34.VLF,(1>.&40.Vsp,)(1?.VR,)R2?.R32.R30.)P,(55.$4;.VR,VHIA,R36.R34.VLF,(1>.&40.Vsp,)(1?.VR,)R2?.R32.R31.)(49.$4;.(48.VR,)(2:.$4;.VR,VHIA,R37.)(5:.R37.R36.R35.R34.R33.R31.R30.)(17.(18.R2=.(3?.&40.R2>.)Vgp,Vtp,R2<.R2;.R2:.Vsp,(3?.&40.R2>.)R29.R28.R27.R26.R25.R24.R23.R22.(3?.&40.R2?.)R1=.R1<.R1;.R1:.(3?.&40.(24.(4<.R2?.+3.)(4=.(48.VR,))))(3?.&40.R2?.)Vs9,Vs10,Vs11,R21.R20.R1?.R1>.)VF,(3?.&40.+:6804.)Vfc,(1:.(6.&40.))R32.(1;.$4;.)))")
(* [comment removed for export] *).
  Proof.
  intros until w2.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SLOT ST24 SThi STlo MI PRES PRES2.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 64) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NEEDR TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 64 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xa6840] [] 137%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 64) :: LF))).
  { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 64) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -80 + 80 <= p \/ p + 1 <= bv_unsigned sp + -80).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NEEDR; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 8 + 8 <= p \/ p + 1 <= sp1 + 8).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1 NEEDR; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NEEDR; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NEEDR; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 15 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  chunk_to_stk SLOT.
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (sp1 + 8), STB : stk _ mf (sp1 + 16) _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SLOT; stk_merge_into ST0 STB; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end.
  }
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  exact HM4.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (xs ys ns ts : list word).
  Hypothesis Han : 1 <= an <= 4999.
  Hypothesis LX : an <= Z.of_nat (length xs). Hypothesis LA : an <= Z.of_nat (length ys).
  Hypothesis LN : an <= Z.of_nat (length ns). Hypothesis LT : 2 * an + 1 <= Z.of_nat (length ts).
  Hypothesis D1 : X + 4 * Z.of_nat (length xs) <= T \/ T + 4 * Z.of_nat (length ts) <= X.
  Hypothesis D2 : A + 4 * Z.of_nat (length ys) <= T \/ T + 4 * Z.of_nat (length ts) <= A.
  Hypothesis D4 : N + 4 * Z.of_nat (length ns) <= T \/ T + 4 * Z.of_nat (length ts) <= N.
  Hypothesis D5 : N + 4 * Z.of_nat (length ns) <= X \/ X + 4 * Z.of_nat (length xs) <= N.
  Hypothesis AL1 : X mod 4 = 0. Hypothesis AL2 : A mod 4 = 0. Hypothesis AL4 : N mod 4 = 0. Hypothesis AL5 : T mod 4 = 0.
  Hypothesis NZ1 : 0 < X. Hypothesis NZ2 : 0 < A. Hypothesis NZ4 : 0 < N. Hypothesis NZ5 : 0 < T.
  Hypothesis T1 : X + 4 * Z.of_nat (length xs) < 2^64. Hypothesis T2 : A + 4 * Z.of_nat (length ys) < 2^64.
  Hypothesis T4 : N + 4 * Z.of_nat (length ns) < 2^64. Hypothesis T5 : T + 4 * Z.of_nat (length ts) < 2^64.
  Hypothesis S1 : X + 4 * Z.of_nat (length xs) <= lo \/ bv_unsigned sp <= X.
  Hypothesis S2 : A + 4 * Z.of_nat (length ys) <= lo \/ bv_unsigned sp <= A.
  Hypothesis S4 : N + 4 * Z.of_nat (length ns) <= lo \/ bv_unsigned sp <= N.
  Hypothesis S5 : T + 4 * Z.of_nat (length ts) <= lo \/ bv_unsigned sp <= T.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X (4 * an).
  Hypothesis CWT : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) T (4 * (2 * an + 1)).
  Hypothesis CRX : client_range L (LB ++ fdata LF) lo X (4 * Z.of_nat (length xs)).
  Hypothesis CRA : client_range L (LB ++ fdata LF) lo A (4 * Z.of_nat (length ys)).
  Hypothesis CRN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "(37.(:.(;.VR,)(<.$3.VLB,(=.VLF,))Vlo,VN,(>.+4.(?.(10.(6.&40.)Vns,))))(15.Pi,$4.P,(15.(36.=R1.)(39.R1.(>.+4.(?.(10.(6.&40.)Vns,)))))(16.$42.(43.$4;.(44.(24.VN,R2.)))$45.)(16.$42.(46.VN,(>.+4.(?.(10.(6.&40.)Vns,))))$45.)))")
(* [comment removed for export] *).
  Hypothesis CRT : client_range L (LB ++ fdata LF) lo T (4 * Z.of_nat (length ts)).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L52616107219.800000ES2sp2lo1P1n2SS1a2Ha1C". (* [comment removed for export] *)
  Lemma cr_sp : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "PP,$4.Pn,$4.P,(:.(;.VR,)(<.$3.VLB,(=.VLF,))Vlo,R2.R1.)P,(37.(36.(24.R3.R2.)Vlo,)(36.(1>.&40.Vsp,)R3.))(:.(;.VR,)(<.$3.VLB,(=.VLF,))(1>.&40.Vsp,)R4.R3.)")
(* [comment removed for export] *).
  Proof. intros P n CR SS a Ha. destruct (CR a Ha) as [C|[C|C]]; [left; clear - C Ha SS; lia| right; left; exact C| right; right; exact C]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "02U0@C17025492443.204C17132796011.206C45137625611.205D10174626805.208D10717101146.208D19813356830.208D23904829926.208D2611090388.208 D35691725366.208D51233741152.208D5472627854.208 D57645839840.208D60109446735.208D62012212072.208D62151899352.208D64899772201.208K13375941723.204K15588900467.204K19288291295.206K21212095580.204K22066676192.206K23238423014.206K35142407091.206K37808760054.206K42475897931.207K42619495643.206K49644543183.205K51284518067.207K63292072926.207K65949573297.206K67183076463.206K68120821232.206K68120821232.208K68120821232.210L10596430123.1  L10895287904.30 L13176305223.2  L13382745852.4  L15598841044.4  L17097970197.4  L17097970840.4  L17097973646.4  L17488828210.1  L17489172274.1  L19283503038.4  L19979721965.30 L20547731588.4  L21218866939.2  L22070643318.3  L22072689504.30 L23250234396.3  L23994278291.6  L24301860020.4  L26892418956.1  L27830289819.1  L28627282501.2  L28776616402.5  L29482428800.30 L31413974788.3  L32431276449.0  L3482562232.30  L35137984549.3  L37802402934.3  L38551529394.0  L40228640085.0  L40281191306.3  L41409160545.3  L42464007210.4  L42623856461.3  L43188064477.2  L43438350703.1  L48173977426.1  L48174174034.1  L49508951760.3  L49656466606.3  L50115922518.30 L50790580594.6  L51126468990.30 L51271447762.4  L52922751378.30 L52941874306.3  L52942107813.30 L53145366927.4  L53147122966.4  L55065323027.30 L55318018650.4  L56056169367.2  L56470958949.3  L56883407412.3  L57389196587.30 L59315053158.5  L60098763854.3  L61380455442.30 L62018535662.1  L63290220894.30 L63290519929.4  L65935405590.3  L67186816014.3  L67228113454.9  L67922604617.0  L68125242982.3  L68132151560.4  L68469750800.3  L7049614941.3   L881835912.0    L9356559645.11  L9631767084.2   O11197253247.206O12422637294.206O13205990919.206O16841474665.203O17025492443.204O17114437730.206O17132796011.206O17223163713.204O22581623065.203O24324186353.203O26481728609.204O27154552881.207O27154552881.209O37672381396.206O45137625611.205O4669439211.206 O49867185343.207O56414299794.206O56615372826.206O56615372826.208O56615372826.210O5730970265.206 O59625529265.206O6173555671.207 O62303909793.203O63817676124.206O6623488489.206 O67018931761.207P20540903971.203P21212095580.204P24300234259.203P31415592355.206P41419110342.206P49494783095.203P49644543183.205P52940256805.206P53135207799.207P53135207799.209P56881789075.206P67183076463.206P68120821232.208P68120821232.210P68483919543.203Q15766564435.208Q17582764468.208Q19813356830.208Q23904829926.208Q34964382778.208Q42716251647.208Q43792049110.208Q48360113622.208Q51233741152.208Q5472627854.208 Q55352487251.208Q60836871818.208Q9356855943.186 Q9644583048.208 Q9706276944.208 00000100200300400500a01J01K01L02802a02b03T04?05`05a06N07;07\07]08f09W0:`0;Q0<20=;0=<0=]0>D0>f0>g0@00@10@20@60@m0A50A60A70AE0AS0Aa0Ae0Ai0Aj0Bf0Bg0Bh0Bi0CC0CD0CS0CT0CX0C\0Cb0Cn0Dd0De0Df0E`0Ea0Eb0Ec0Ed0Em0En0Eo0F00F80F<0F@0FD0FE0FF0G=0GT0HK0HL0I>0I?0I[0I\0I]0J10J?0JE0JN0JO0Jf0K<0KF0L@0LC0M:0M;0M<0M=0M]0M^0M_0M`0Ma0Ml0Mm0NX0N_0N`0Na0Nb0Nc0Nd0Ne0Nf0Ng0Nh0Ni0Nj0Nk0Nl0Nm0Nn0No0O00O10O20O30O40O50O60O70O80O90O:0O;0P=0P>0QE0R>0Ra0SZ0S[0T>0T?0T@0U90U:0U;0U<0V50VV0W30WL0Wb0XP0XQ0Xn0YP0Yi0Z?0Z@0ZA0Z^0[80[9FFFFFS2LF2ra2sp1X1A1N2an1T3LFB2xs2ys2ns2ts2FB3sp1S2LF2ra2sp1X1A1N1T3LFB2xs2ys2ns2ts2FB3sp1FFS2LF2ra2sp1X1A1N2an1T3LFB2xs2ys2ns2ts2FB3sp1S2LF2ra2sp1X1A1N1T3LFB2xs2ys2ns2ts2FB3sp1FS1R2LF2ra2sp1X1A1N1T2lo3LOS3LFB2xs2ys2ns2ts2FB3sp1S1R2LF2ra2sp1X1A1N1T3LFB2xs2ys2ns2ts2FB3sp1S1R3HIA1h2LF2ra2sp1X1A1N1T2lo3TOP3LFB2xs2ys2ns2ts3NZ13NZ23NZ43NZ53SPR2FB3sp12h13SP15Ehtop4SP1R2F0FS2LF2sp2an1T2lo3LFB2xs2ys2ns2ts2LT2S53sp13SP1S2LF2sp1X2an2lo3LFB2xs2ys2ns2ts2LX2S13sp13SP1S2LF1X2an1T3LFB2xs2ys2ns2ts2LX2D1FS1R3HIA2LB2LF1X2an1T2lo3LFB2xs2ys2ns2ts2LT2FB3sp12h13x143APT3x153x164POSTS1R5NEEDR2LF2sp1X2an2lo3SLO3LFB2xs2ys2ns2ts2LX2S1S1R3HIA2LB2LF1X2an1T2lo3LFB2xs2ys2ns2ts2LX2FB3sp12h13x143APX3x153x164POSTS1R5NEEDR2LF2sp2an1T2lo3SLO3LFB2xs2ys2ns2ts2LT2S5S2LF1X1N2an3LFB2xs2ys2ns2ts2LX2D5S1R3HIA2LB2LF1X2an1T2lo3LFB2xs2ys2ns2ts2LT2FB3sp12h13x143APT3x153x164POSTFS2LF1N2an1T3LFB2xs2ys2ns2ts2LT2D4S2LF2sp1N2lo3LFB2xs2ys2ns2ts2S43sp13SP1S2LF2sp2lo3LFB2xs2ys2ns2ts3sp13SP1FS1R3HIA2LB2LF1X2an1T2lo3LFB2xs2ys2ns2ts2LX2FB3sp12h13x143APX3x153x164POSTFFS2FBS1R5NEEDR2sp1A2lo3SLO2xs2ys2ns2ts2S22FB3sp13SP12F04FBLOS2lo3sp1FFS2an2ys3Han2LAS2an2ns3Han2LNS2an2xs3Han2LXS2nsS2ysFS1R3HIA5NEEDR1h2sp2lo3SLO3TOP2xs2ys2ns2ts2FB3sp13SP12F04FBLOFFFS1T2xs2ys2ns2ts2FB3sp13APTFS1P1n1k2Hk1a2HaFS2spS2FBS2an1TS1N2an2ns2LNS1R5NEEDR2sp2lo3SLO2xs2ys2ns2ts3ACV2FB3sp13SP12F14FBLOFSS1R5NEEDR2sp2lo3SLO2xs2ys2ns2ts2FB3sp13SP14SP1M2F02F84FBLOFFSSS1R3HIA1hFFFS2lo3sp1S2FBS2xsS2tsFFS1R5NEEDR2sp1T2lo3SLO2xs2ys2ns2ts2S52FB3sp13SP12F04FBLOS1R5NEEDR2sp2lo3LOS3SLOS1R5NEEDR2sp1X2lo3SLO2xs2ys2ns2ts2S12FB3sp13SP12F04FBLOFS1R5NEEDR2sp2lo3SLO2xs2ys2ns2ts2FB3sp13SP12F04FBLOFS2lo2xs2ys2ns2ts2FB3sp14FBLOFFS2xs2ys2ns2ts2FB3sp1S2an2ts3Han2LTS1X2anS2ns1i2HiFS2xs2ys2ns2ts2FB3sp12F0S2an2xs3Han2LX1C2ts2LTS1R2lo3LOSS1R5NEEDR2sp2lo3SLO2xs2ys2ns2ts2FB3sp13SP14SP1M2F02F84FBLOS1RS1R5NEEDR2sp1N2lo3SLO2xs2ys2ns2ts2S42FB3sp13SP12F04FBLOFFFS1R3HIA1h2sp2lo3TOP4HTOP3sp13SP1SFFFS2sp2lo3sp1SS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S2FB2F0FFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R5NEEDR2LF2sp2an1T2lo3SLO3LFB2xs2ys2ns2ts2LX2LA2LN2LT2S53sp13SP1FS1R5NEEDR2LF2sp1X2an1T2lo3SLO3LFB2xs2ys2ns2ts2LX2LN2LT2D12S12S53sp13SP1S1R5NEEDR2LF2sp2an1T2lo3SLO3LFB2xs2ys2ns2ts2LT2S53sp13SP1S2LF2lo3LFB2xs2ys2ns2ts2FB3sp14FBLOS1R5NEEDR2LF2sp2an1T2lo3SLO3LFB2xs2ys2ns2ts2LT2S53sp13SP1FS2LF2lo3LFB2xs2ys2ns2ts2FB3sp14FBLOFFS1R5NEEDR2LF2sp1X2an2lo3SLO3LFB2xs2ys2ns2ts2LX2S13sp13SP1FFFS1R5NEEDR2LF2sp1X2an2lo3SLO3LFB2xs2ys2ns2ts2LX2S13sp13SP1S1R2LF2lo3LOS3LFB2xs2ys2ns2ts3ALOS2LF2an1T3LFB2xs2ys2ns2ts3HanS2LF2an1T3LFB2xs2ys2ns2tsS2LF1T3LFB2xs2ys2ns2tsS1R5NEEDR2LF2sp2lo3SLO3LFB2xs2ys2ns2ts3sp13SP1FS2LF1X2an3LFB2xs2ys2ns2ts3HanS2LF2sp2lo3LFB2xs2ys2ns2ts3sp13SP1S2LF1X2an3LFB2xs2ys2ns2tsS2LF1X3LFB2xs2ys2ns2tsFFS2LF3LFB2xs2ys2ns2ts3sp14SP1RS2LF3LFB2xs2ys2ns2ts2FB2F0F". (* [comment removed for export] *)
  Lemma fm_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)P,(29.$4;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(9.$4;.Vm,VX,Vxs,)P,(34.$4;.Vm,VA,(35.Vys,))P,(34.$4;.Vm,VN,(35.Vns,))P,(9.$4;.Vm,VT,Vts,)P,(1=.$4;.Vm,Vlo,(1>.&40.Vsp,))P,(1<.$4;.Vm,)P,(47.$4;.(48.VR,)(2:.$4;.VR,VHIA,Vh,)Vm,VX,(>.+4.Van,))P,(47.$4;.(48.VR,)(2:.$4;.VR,VHIA,Vh,)Vm,VA,(>.+4.Van,))P,(47.$4;.(48.VR,)(2:.$4;.VR,VHIA,Vh,)Vm,VN,(>.+4.Van,))P,(47.$4;.(48.VR,)(2:.$4;.VR,VHIA,Vh,)Vm,VT,(>.+4.(24.(>.+2.Van,)+1.)))(49.$4;.(48.VR,)(2:.$4;.VR,VHIA,Vh,)(4:.$4;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs,Vts,Vlo,Vm,)(17.(18.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(3?.&40.VX,)(3?.&40.VA,)(3?.&40.VN,)(3?.&40.Van,)Vmmw,(3?.&40.VT,)R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(3?.&40.$57.)Vfc,(1:.(6.&40.))Vm,(1;.$4;.)))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a6 a7 t3 t4 t5 t6 HH HX HA HN HT ST MI OX OA ON OT.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    eapply evtA_cut.
    { eapply pro_walk; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & w0 & w1 & w2
                   & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & LMB & FSHX
                   & SAVE & SLOT & ST8 & SThi & STlo & MI1 & PRES0).
    subst ms1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS. change (64 - 40) with 24 in IND.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (cr_sp _ _ CRX S1) as CRXs. pose proof (cr_sp _ _ CRA S2) as CRAs. pose proof (cr_sp _ _ CRT S5) as CRTs.
    (* [comment removed for export] *)
    pose proof (presA_u32arr asegs R _ _ _ _ _ _ m m1 X xs HP01 HX CRXs I) as HX1.
    pose proof (presA_u32arr asegs R _ _ _ _ _ _ m m1 T ts HP01 HT CRTs I) as HT1.
    assert (HA1 : bytes_at asegs m1 A (u32s ys)).
    { eapply (presA_bytes_at asegs R); [exact HP01| exact HA| rewrite u32s_length; replace (Z.of_nat (4 * length ys)) with (4 * Z.of_nat (length ys)) by (clear; lia); exact CRAs| exact I]. }
    assert (HN1 : bytes_at asegs m1 N (u32s ns)).
    { destruct CRN as [CRNc|[RON _]].
      - eapply (presA_bytes_at asegs R); [exact HP01| exact HN| rewrite u32s_length; replace (Z.of_nat (4 * length ns)) with (4 * Z.of_nat (length ns)) by (clear; lia); exact (cr_sp _ _ CRNc S4)| exact I].
      - eapply static_limbs_any_mem; [exact MI| exact MI1| exact HN|]. rewrite u32s_length. intros i Hi. apply RON. clear - Hi. lia. }
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros xq Hx; eapply hcs_below_top; exact Hx).
    assert (SUBCR : forall P n k, client_range L (LB ++ fdata LF) (bv_unsigned sp) P n -> 0 <= k <= n -> client_range L (LB ++ fdata LF) (bv_unsigned sp) P k)
      by (intros P n k CR Hk a Ha; apply CR; clear - Ha Hk; lia).
    assert (OX1 : aobj asegs AL CS m1 X (4 * an)) by (eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OX| eapply SUBCR; [exact CRXs| clear - Han LX; lia]| clear - LOS SLO NEEDR; lia| exact TOPCS]).
    assert (OA1 : aobj asegs AL CS m1 A (4 * an)) by (eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OA| eapply SUBCR; [exact CRAs| clear - Han LA; lia]| clear - LOS SLO NEEDR; lia| exact TOPCS]).
    assert (ON1 : aobj asegs AL CS m1 N (4 * an)).
    { destruct CRN as [CRNc|[_ NZN]].
      - eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact ON| eapply SUBCR; [exact (cr_sp _ _ CRNc S4)| clear - Han LN; lia]| clear - LOS SLO NEEDR; lia| exact TOPCS].
      - assert (ONF : aobj asegs AL CS m1 N (4 * Z.of_nat (length ns))).
        { eapply (AImgGlobals.aobj_img asegs AL); [| eapply (hm_img_shadow asegs R HIA); exact HH1| exact NZN].
          destruct IMG as (G & LO' & HI' & GSB). eapply img_cs_of; [exact LO'| exact HI'| exact G| exact GSB|].
          intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA h); assumption. }
        eapply aobj_sub; [exact ONF| apply Z.le_refl| clear - Han LN; lia]. }
    assert (OT1 : aobj asegs AL CS m1 T (4 * (2 * an + 1))) by (eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OT| eapply SUBCR; [exact CRTs| clear - Han LT; lia]| clear - LOS SLO NEEDR; lia| exact TOPCS]).
    (* [comment removed for export] *)
    assert (APX : FB + 64 <= X \/ X + 4 * Z.of_nat (length xs) <= FB).
    { destruct (frame_apart_obj0 R HIA LB LF lo X (4 * Z.of_nat (length xs)) FB 64 FRSH CRX ltac:(clear; lia) ltac:(clear; lia) LOS) as [C|C]; [exfalso; clear - C Han LX; lia| exact C]. }
    assert (APT : FB + 64 <= T \/ T + 4 * Z.of_nat (length ts) <= FB).
    { destruct (frame_apart_obj0 R HIA LB LF lo T (4 * Z.of_nat (length ts)) FB 64 FRSH CRT ltac:(clear; lia) ltac:(clear; lia) LOS) as [C|C]; [exfalso; clear - C Han LT; lia| exact C]. }
    (* [comment removed for export] *)
    assert (BL : u32arr asegs m1 (FB + 32) [Z_to_bv 64 1]).
    { eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 1))); [eapply rw_cells_reshape; [exact LMB| cbn; split; [apply (length_le4 (Z_to_bv 64 1))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity]. }
    pose proof (u32arr_ro _ _ _ _ BL) as HB1.
    assert (OB1 : aobj asegs AL CS m1 (FB + 32) (4 * 1)).
    { eapply (aobj_of_partial_shadow_sh asegs AL CS m1 FB _ (FB + 32) 4%nat 4); [exact CSOK| exact FSHX| eapply crange_sub; [exact CFB| clear; lia| clear; lia]| exact F8| clear - F0; lia| clear; lia| clear; lia| reflexivity]. }
    assert (CWX1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) (arl_stklo R) (htop asegs R HIA h) X (4 * an))
      by (eapply client_wrange_mono; [exact CWX| intros b' Hb; apply fdata_cons_sub; exact Hb]).
    assert (CWT1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) (arl_stklo R) (htop asegs R HIA h) T (4 * (2 * an + 1)))
      by (eapply client_wrange_mono; [exact CWT| intros b' Hb; apply fdata_cons_sub; exact Hb]).
    (* [comment removed for export] *)
    assert (PRES : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [(X, X + 4 * an); (T, T + 4 * (2 * an + 1))] m m1).
    { destruct PRES0 as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_weaken; [exact P0| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xq _; exact I]. }
    clear PRES0 HP01.
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCX : wcover R LB LF (bv_unsigned sp) [(X, X + 4 * an); (T, T + 4 * (2 * an + 1))] X (4 * an)) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WCT : wcover R LB LF (bv_unsigned sp) [(X, X + 4 * an); (T, T + 4 * (2 * an + 1))] T (4 * (2 * an + 1))) by (apply wcover_inside; cbn [inside]; right; left; clear; lia).
    assert (SCS1 : crange CS lo (sp1 - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SP1 TOP HTOP; lia]).
    pose proof MM as MM'. unfold mpi_core_montmul_stmtA, A_MPI_CORE_MONTMUL, MPI_CORE_MONTMUL_STACK_A in MM'.
    unfold A_MPI_CORE_MONTMUL. rewrite <- Ehcs.
    callxA_sp sp1 (eapply MM' with (h := h1) (LB := LB) (LF := (FB, 64) :: LF) (X := X) (A := A) (B := FB + 32) (bn := 1) (N := N) (an := an) (T := T) (lo := lo)
                                   (xs := xs) (ys := ys) (zs := [Z_to_bv 64 1]) (ns := ns) (ts := ts);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehcs, ?Ehtop;
                   first [ exact HH1 | exact HX1 | exact HA1 | exact HB1 | exact HN1 | exact HT1 | exact STlo | exact LOS | exact MI1 | exact OX1 | exact OA1 | exact OB1 | exact ON1 | exact OT1
                         | exact CWX1 | exact CWT1 | exact Han | exact LX | exact LA | exact LN | exact LT | exact D1 | exact D2 | exact D4 | exact D5
                         | exact AL1 | exact AL2 | exact AL4 | exact AL5 | exact NZ1 | exact NZ2 | exact NZ4 | exact NZ5 | exact T1 | exact T2 | exact T4 | exact T5 | reflexivity
                         | (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SP1 SP1M SLO NEEDR TOP F0 F1 F8 FBLO ACV APT S1 S2 S4 S5; first [lia| Z.div_mod_to_equations; lia])
                         | match goal with |- ?g => idtac "MM-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "MM-LEFT:" g end.
    rewrite Ehcs.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA h1 _ _ m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : u32arr asegs m2 X ?l, H2 : length ?l = length xs, H3 : skipn _ ?l = skipn _ xs |- _ => rename H into HX2; rename H2 into LX2; rename H3 into SKX2; rename l into xs2 end.
    match goal with H : u32arr asegs m2 T ?l, H2 : length ?l = length ts, H3 : skipn _ ?l = skipn _ ts |- _ => rename H into HT2; rename H2 into LT2; rename H3 into SKT2; rename l into ts2 end.
    pose proof (presW_init_at R HIA h1 _ _ LB LF m2 (bv_unsigned sp) (arl_stklo R) [] h HH2
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros xq Hx; rewrite Ehcs; exact Hx) Estk ltac:(clear; lia)) as PRES2.
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m m2 PRES ltac:(intros xq Hx; rewrite Ehcs; exact Hx) Estk) as PRESh1.
    (* [comment removed for export] *)
    pose proof (conj HX2 I) as HX2b. pose proof (conj HT2 I) as HT2b. clear HX2 HT2.
    eapply evtA_cut.
    { eapply evtA_cs_mono.
      { eapply epi_walk with (h3 := h1) (LBa := LB) (LBb := LB) (m0 := m) (m2x := m2) (WA := [(X, X + 4 * an); (T, T + 4 * (2 * an + 1))]) (WB := []);
          first [ exact HH2 | exact PRESh1 | exact PRES2 | exact FRSH | exact CFB | exact AP | exact Ehtop | exact Estk | eassumption | reflexivity
                | lazymatch goal with |- forall x, _ -> _ => first [intros xq Hx; rewrite Ehcs; exact Hx| intros b' Hb; exact Hb] end
                | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
      intros xq Hx; rewrite Ehcs in Hx; exact Hx. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    destruct HX2b as [HX2 _]. destruct HT2b as [HT2 _].
    pose proof (presW_presA asegs R HIA h1 LB LF _ _ _ _ _ PRES29) as HP29.
    apply evtA_done. unfold mpi_core_from_mont_rep_postA.
    do 15 eexists. exists m9, h4, xs2, ts2.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|].
    split; [pose proof (presW_presA asegs R HIA h1 LB LF _ _ _ _ _ PRES9) as HPF; rewrite Estk in HPF; exact HPF|].
    split; [eapply (presA_u32arr asegs R); [exact HP29| exact HX2| rewrite LX2; exact CRXs| exact I]|].
    split; [exact LX2|]. split; [exact SKX2|].
    split; [eapply (presA_u32arr asegs R); [exact HP29| exact HT2| rewrite LT2; exact CRTs| exact I]|].
    split; [exact LT2|]. split; [exact SKT2|].
    split; [exact HH4|].
    split; [rewrite E4cs; exact Ehcs|]. split; [rewrite E4top; exact Ehtop|]. split; [rewrite E4stk; exact Estk|].
    split; [rewrite E4flag; exact Eflag|]. split; [rewrite E4vol; exact Evol|]. split; [rewrite E4fr; exact Efr|].
    intros mo9. split; intros K; [apply (proj1 (HKI mo9)), (proj1 (HKI4 mo9)), K| apply (proj2 (HKI4 mo9)), (proj2 (HKI mo9)), K].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  Theorem A_mpi_core_from_mont_rep_spec_s : mpi_core_from_mont_rep_stmtA asegs R HIA A_MPI_CORE_FROM_MONT_REP.
  Proof.
    unfold mpi_core_from_mont_rep_stmtA. intros until ts.
    intros HH LFB HX HA HN HT Han LX LA LN LT D1 D2 D4 D5 AL1 AL2 AL4 AL5 NZ1 NZ2 NZ4 NZ5 T1 T2 T4 T5 ST LOS SLO SLOS TOP SPA TPV S1 S2 S4 S5
           CWX CWT CRX CRA CRN CRT MI RAE OX OA ON OT -> -> -> -> ->.
    unfold MPI_CORE_FROM_MONT_REP_STACK_A in SLO.
    eapply fm_main with (xs := xs) (ys := ys) (ns := ns) (ts := ts); eassumption.
  Qed.
End WalkF.

Theorem A_mpi_core_from_mont_rep_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_from_mont_rep ()) "PR,$2.PHIA,(5;.$4;.R1.)P,(5<.(48.R2.))P,(16.$4.(5=.R3.)$5>.)P,(16.$4.(5?.R4.=)$60.)P,(36.=(3>.R5.))P,(36.=(3=.R6.))P,(61.$4;.R7.R6.$4>.)(62.$4;.R8.R7.$57.)")
(* [comment removed for export] *).
Proof. intros. apply A_mpi_core_from_mont_rep_spec_s; assumption. Qed.

(* [comment removed for export] *)

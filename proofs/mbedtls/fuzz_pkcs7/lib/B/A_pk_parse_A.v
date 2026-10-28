(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00d3edbe2b9f763d 1 1 32 3 1 1 80 1 83 1 10 40 1 45 1 64 1 70 1 71 1 72 1 73 1 81 1 82 1 84 32P042a9e05cfe757f6 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P0474642937fa4fe5 1 1 32 3 0 1 79 1 82 1 10 39 1 44 1 63 1 69 1 70 1 71 1 72 1 80 1 81 1 83 32P061c601a9f0e07bd 1 1 64 2 0 1 79 1 3 6 1 80 1 81 64P06d33523d99575f6 1 1 16 3 1 1 24 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P07062e38e9d0a58d 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P071cbc049ba66014 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P083e22287fbaeb6e 0 6 0 1 69 1 70 1 72 1 79 1 80 1P08bee5a366cdc8e4 1 1 32 3 0 1 80 1 83 1 10 40 1 45 1 64 1 70 1 71 1 72 1 73 1 81 1 82 1 84 32P09a6f96dc7ca66ec 1 1 16 3 1 1 24 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P09d4729989daa991 0 6 0 1 45 1 46 1 48 1 55 1 56 1P0a457db51d9bed4e 0 8 0 1 39 1 69 1 70 1 71 1 72 1 79 1 80 1P0aa2524e361139d1 0 7 0 1 39 1 69 1 70 1 72 1 79 1 80 1P0ac43d9c8b006ea5 0 6 0 1 45 1 46 1 48 1 55 1 56 1P0ac8f443de3c519f 0 4 0 16 3 16 55 16 56 16P0addaa235bdaccd9 0 4 0 1 44 1 55 1 56 1P0b18eb1d1b26bb8a 0 6 0 1 45 1 46 1 48 1 55 1 56 1P0b1e4e55e4b8de14 0 3 0 1 39 1 45 1P0c2a168ab39de763 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P0c6c408dd5eb342d 0 6 0 1 45 1 46 1 48 1 55 1 56 1P0c91019921191edb 1 1 16 2 1 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P0cc5c41c3b92f373 0 4 0 1 44 1 55 1 56 1P0cd5a09d5da172e2 0 4 0 1 44 1 55 1 56 1P0d5a1d1b96d0f29a 0 6 0 1 45 1 46 1 48 1 55 1 56 1P0e119593622c4e39 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P0e295cbb4b6ead86 1 1 16 3 0 1 80 1 81 1 4 58 2 79 2 82 2 83 32P0e950841ae4e4a07 1 1 16 2 1 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P0fcd63b1e511db44 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0fec1a89271b23b6 1 2 32 3 0 1 80 1 83 1 32 3 1 1 81 1 82 1 2 84 2 85 2P1008ada3d79d75d8 0 4 0 1 44 1 55 1 56 1P10d3c1dad1ed4a2b 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P113efb95be55422e 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P115e6a371a78ed9b 0 4 0 1 44 1 55 1 56 1P11c40c2232a93433 1 1 16 3 1 1 24 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P11e7536167082319 1 1 32 3 0 1 79 1 82 1 10 39 1 44 1 63 1 69 1 70 1 71 1 72 1 80 1 81 1 83 32P1210b9b5c9c87d3e 1 2 16 3 1 1 24 1 56 1 16 3 0 1 25 1 57 1 2 58 1 59 1P12abca88ce501d30 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P15037a0f5bc65658 0 4 0 1 44 1 55 1 56 1P158433866e0996e7 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P15ebabdb96037590 1 1 16 3 0 1 81 1 82 1 4 59 2 80 2 83 2 84 32P1616a0479850d34b 0 7 0 1 39 1 69 1 70 1 72 1 79 1 80 1P176fb7099c33ec7a 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P17c397eae95d9985 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P188e2d3d6edc49e3 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P1954e002d448454c 1 1 16 2 1 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P1a4b4fecccddbec3 1 1 16 3 0 1 81 1 82 1 9 45 4 64 4 70 4 71 4 72 4 73 4 80 4 83 4 84 64P1a7900ffe229961e 1 1 64 2 5 1 79 1 3 0 1 80 1 81 64P1b131bad7d29e389 1 2 16 3 1 1 24 1 56 1 16 3 0 1 25 1 57 1 2 58 1 59 1P1b888bee62587968 1 1 16 3 1 1 24 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P1b95c490fd949097 1 1 32 3 0 1 80 1 83 1 10 40 1 45 1 64 1 70 1 71 1 72 1 73 1 81 1 82 1 84 32P1c3b5e3734af944c 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P1d6e02d20d4fb8a1 0 4 0 1 44 1 55 1 56 1P20f082e7b56e10a2 0 6 0 1 45 1 46 1 48 1 55 1 56 1P2249fb88b55f6c70 1 1 16 3 0 1 80 1 81 1 4 58 2 79 2 82 2 83 32P229ce30410ea175c 1 2 32 3 0 1 80 1 83 1 32 3 1 1 81 1 82 1 2 84 2 85 2P236db0f39edffc16 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2461a20e688750ab 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P24bfeff774e617e8 1 2 16 3 1 1 24 1 56 1 16 3 0 1 25 1 57 1 2 58 1 59 1P25017ce6e96f5737 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P25cce8b8091c3f1f 0 6 0 1 45 1 46 1 48 1 55 1 56 1P2668adb85b884ee0 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P266c9b25556331ab 1 1 16 3 0 1 81 1 82 1 9 45 4 64 4 70 4 71 4 72 4 73 4 80 4 83 4 84 64P26be50e4ce0932fb 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P2768a8cc423ce3ed 0 6 0 1 55 1 58 1 68 1 79 1 80 1P27c5a4a062ec3e51 1 1 16 2 1 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P28e1a5e02bdf5642 1 1 16 3 1 1 24 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P28e64ab0c475ae8d 1 2 16 3 1 1 24 1 56 1 16 3 0 1 25 1 57 1 2 58 1 59 1P29659c9a4b8ae17c 0 4 0 1 44 1 55 1 56 1P29c5f5ec19f4a326 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P2ba0a957ed61206d 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P2bd8ccebe4c2938c 1 2 16 3 1 1 24 1 56 1 16 3 0 1 25 1 57 1 2 58 1 59 1P2bf5f2ff939d2a4f 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P2c0b4e042e670981 1 1 16 3 0 1 80 1 81 1 9 44 4 63 4 69 4 70 4 71 4 72 4 79 4 82 4 83 64P2c21ffe5e03168a8 0 6 0 1 45 1 46 1 48 1 55 1 56 1P2c44939a746af326 1 2 16 3 1 1 24 1 56 1 16 3 0 1 25 1 57 1 2 58 1 59 1P2cb165f01247c6f9 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2cea3e17eb375263 0 4 0 1 44 1 55 1 56 1P2cf68bdb7bae1e32 1 1 16 2 1 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P2d71192624e3c7ee 0 6 0 1 45 1 46 1 48 1 55 1 56 1P2dcccf60a5d53376 0 6 0 1 45 1 46 1 48 1 55 1 56 1P2e1c67de02500232 1 1 16 2 1 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P2e89776ffea85ae9 1 1 16 2 1 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P2f81e76ac3aa0aeb 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P3116c4609f06747e 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P313632c71b69c632 1 2 16 3 1 1 24 1 56 1 16 3 0 1 25 1 57 1 2 58 1 59 1P3298de19570519a5 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P331bc15b60045c84 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P33b09a7cd82d53b6 1 1 16 2 0 1 55 1 3 4 1 56 1 57 16P33d672602e45ac2f 0 4 0 1 44 1 55 1 56 1P34b7daf5c626dfcc 0 3 0 1 29 1 38 1P35bfa4df323bb4e1 0 4 0 1 44 1 55 1 56 1P35d88e01045a5fac 1 1 16 3 1 1 24 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P376594faeffdeb33 1 1 32 3 0 1 80 1 83 1 10 40 1 45 1 64 1 70 1 71 1 72 1 73 1 81 1 82 1 84 32P379a488009dfa813 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P37ad738856cfb18a 0 4 0 1 44 1 55 1 56 1P38c9168af54c14de 1 1 32 3 1 1 80 1 83 1 10 40 1 45 1 64 1 70 1 71 1 72 1 73 1 81 1 82 1 84 32P3950b8d4714a2f1d 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3951223228980675 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P395fd0a4acb62651 0 6 0 1 45 1 46 1 48 1 55 1 56 1P3984641abceb5b62 0 6 0 1 45 1 46 1 48 1 55 1 56 1P3a2a463a6069fc65 1 2 32 3 0 1 80 1 83 1 32 3 1 1 81 1 82 1 2 84 2 85 2P3a7bbcaf1eec51c9 1 1 16 3 1 1 24 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P3b0e96e8153307dd 0 7 0 1 45 1 46 1 47 1 48 1 55 1 56 1P3b3a5d0cb13ed483 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P3b4f597e7f4e1a24 0 4 0 1 44 1 55 1 56 1P3bb5c9fcb713761c 0 4 0 1 44 1 55 1 56 1P3cb2d194eb9870e0 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3cc668a2d9032ec4 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P3cc7d8030a9cd02d 1 1 32 3 0 1 79 1 82 1 10 39 1 44 1 63 1 69 1 70 1 71 1 72 1 80 1 81 1 83 32P3cff55c0f949683d 0 6 0 1 45 1 46 1 48 1 55 1 56 1P3f1ba69f75507182 1 1 16 4 1 1 26 1 35 1 56 1 8 38 1 40 1 46 1 47 1 48 1 49 1 57 1 58 16P3f79c08350904946 0 6 0 1 45 1 46 1 48 1 55 1 56 1P3f7b489e02f32d0f 1 1 16 3 0 1 81 1 82 1 9 45 4 64 4 70 4 71 4 72 4 73 4 80 4 83 4 84 64N00727a40bda60ed8N00b20c95f88c4176N00e89cf5d0fb699eN01504a1fc1690b2aN022a39900aa13e51N026eead610371b11N02a9dab62dec9aa4N037ea65174d8a24fN0590f26384c2f8dcN05a304387a6b0aa1N0637b79d2f563588N06a2ce6535025e68N085645b6f9c04af9N09f59b61772088c5N0adfba9bbd0ca987N0b20a3fe2984ac2bN0b2b88f1336c012fN0b65aeb553b815c5N0da574ba50d37405N0e13d0ab831d6d35N0fe605f56aa8ad3cN0ffa9fd332b8784aN106c34573aeb344aN10bbca7ad4aa2539N10cee33678f22f76N1105235aeb50ebeeN1216ea122ee2141bN13b6a5413453ad4dN15405b88943bd46eN169e3db2ff53887bN17b1be97f1a64c34N191a5a3ab845bd6dN1a5ef7581760f8f6N1b3779b64b955e84N1d2283cf9bd9a326N1ec7596a04a29ed6N1f72bce1a2a86ab8N206e72385101e006N20a0c7d1ef669e09N20d29b51eef6020dN2214a872e402cbb2N224c6780d5faaefaN23bef8a1445e1fc8N2448141c61d073d1N250bd6072a2046b5N25a4bfa91e0155f8N26906a6c1c591c18N2735db3145557bdcN27840c615d4c79ecN279b8e0fd3f02116N28605549968f6817N294faeb80c517abbN29d6bc465d65054eN2a3119f012796fd7N2b9cee798dfc3200N2bb5a065d04ead34N2da13c56f0ddb83aN2e05ffd93f5fddaaN2e1e62ae6db20e0bN2eb9baffdcb74273N31652b2de4457d19N32014837c1e51e19N3309b782a692cc5bN34647590668dd1daN35ddc9ba07c79aa9N36bbc7dc4d872140N37fa58d2e484125dN385d87f057df5b2dN3927881574d4e185N3960701f92601e36N39ebb23e6d8ae2bfN39fd256602e548e5N3b08a2a0c60ce3a3N3d21f582ecac9b24N3e148ad591692ee8N3f5f688a89e76709N3f8ac7d292e98087N3fc0e6d72e2c271a"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
(* [comment removed for export] *)
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
Ltac chunk_split H n H1 H2 ::=
  lazymatch type of H with
  | OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells ?sg ?mx ?A ?cs =>
      let pre := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.firstn n cs) in
      let post := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.skipn n cs) in
      change (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx A (Corelib.Init.Datatypes.app pre post)) in H;
      apply (proj1 (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.CellsX.rw_cells_app sg mx A pre post)) in H;
      destruct H as [H1 H2];
      let z := eval cbv in (Stdlib.ZArith.BinInt.Z.of_nat (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.cells_size pre)) in
      change (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx (Stdlib.ZArith.BinInt.Z.add A z) post) in H2
  end.
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
Ltac2 gd_tbl_A_pk_parse_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkPKA.Call.S1P"; "A_PK_PARSE_SUBPUBKEY"].


Definition A_PK_PARSE_SUBPUBKEY : Z := 0x0b0158.    (* [comment removed for export] *)
Definition A_SMALLOC_2_PK : Z := 0x531fc.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT_PK : Z := 0x0f5ea8.             (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cb_step H :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A ?l =>
    let rec find pre l :=
      lazymatch l with
      | CB 8 ?bs :: ?post => apply (rw_cells_CB8_C8 sg mx A pre bs post) in H; cbn [app] in H
      | CB 4 ?bs :: ?post => apply (rw_cells_CB4_C4 sg mx A pre bs post) in H; cbn [app] in H
      | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in find pre' post
      end in find (@nil cell) l
  end.
Ltac cb_all H := repeat (cb_step H).

Section WalkPKA.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_PK.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_PK.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP END PKA lo STKk : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis STK0 : 176 + arl_need_smalloc R <= STKk.
  Hypothesis SLO : lo <= bv_unsigned sp - STKk.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis PKB : 0 <= PKA /\ PKA + 16 <= 2^64.
  Hypothesis ENDB : 0 <= END < 2^64.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_PK in UARG; unfold A_SMALLOC_2_PK in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation F1 := (C1 (Z_to_bv 8 241)). Local Notation F2 := (C1 (Z_to_bv 8 242)). Local Notation F3 := (C1 (Z_to_bv 8 243)).
  Local Notation F8 := (C1 (Z_to_bv 8 248)). Local Notation Z0 := (C1 (Z_to_bv 8 0)). Local Notation P4 := (C1 (Z_to_bv 8 4)).
  Local Notation FSH0 :=
    [F1; F1; F1; F1;  F8; F8; F2; F2;  F8; F8; F8; F2;  F2; F2; F2; F2;  Z0; F2; F2; F2;  Z0; Z0; Z0; F2;  F2; F2; F2; F2;  P4; F2; P4; F3].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := fun ms =>
    exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem)
      (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w0 w1 w2 pc0 pc1 lenj kpad gpad w8 w16 w24 : word)
      (jpar : list (bv 8)),
    ms = MS (mkR (Z_to_bv 64 0xb01d0) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1)
               a0 (Z_to_bv 64 END) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 PKA) (Z_to_bv 64 (FB + 64))
               s7 s8 s9 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
            F (Z_to_bv 64 0xb02c0) fc None m1 (seg_rom asegs)
    /\ (bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160)
    /\ sp1 mod 32 = 0
    /\ HM asegs R HIA h1 LB ((FB, 256) :: LF) m1
    /\ hcs asegs R HIA h1 = hcs asegs R HIA h
    /\ htop asegs R HIA h1 = htop asegs R HIA h
    /\ hstkhi asegs R HIA h1 = hstkhi asegs R HIA h
    /\ hflag asegs R HIA h1 = hflag asegs R HIA h
    /\ havol asegs R HIA h1 = havol asegs R HIA h
    /\ hfr asegs R HIA h1 = hfr asegs R HIA h
    /\ (forall mo : Model, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo)
    /\ FB mod 64 = 0
    /\ fresh_apart R LB LF FB 256
    /\ rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
    /\ rw_cells asegs m1 (FB + 32) [C8 pc0; C8 pc1]
    /\ rw_cells asegs m1 (FB + 64) [C8 lenj]
    /\ rw_cells asegs m1 (FB + 96) [CB 24 jpar]
    /\ rw_cells asegs m1 (FB + 160) [C4 (Z_to_bv 64 0); C4 kpad]
    /\ rw_cells asegs m1 (FB + 176) [C4 (Z_to_bv 64 0); C4 gpad]
    /\ rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL)
         [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
          F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0]
    /\ rw_cells asegs m1 (bv_unsigned sp + -104)
         [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m1 (sp1 + 8) [C8 w8; C8 w16; C8 w24]
    /\ rw_cells asegs m1 (sp1 + 48) [C8 (Z_to_bv 64 FB)]
    /\ stk asegs m1 sp1 (sp1 + 8)
    /\ stk asegs m1 (sp1 + 32) (sp1 + 48)
    /\ stk asegs m1 (sp1 + 56) (bv_unsigned sp + -104)
    /\ stk asegs m1 lo sp1
    /\ mem_inv asegs m1
    /\ presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 ENDB; try lx_pin1 PKB; try lx_pin1 PPB.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02h0@D18607476203.109D2236076691.158 D2457697676.141 D32458983511.141D32604263317.142D3373313673.140 D44547585450.158D45714769720.140D50254960491.110D51038213418.110D54771307690.168D558665111.79   D57793146470.158D57793146470.168D60765385619.168D62009822325.79 D62011770190.142D66237105961.141D68405032138.140D6909683407.140 L15822417165.1  L1685717371.0   L18021517688.12 L19546883925.125L19980016842.12 L21850448153.153L21866712442.1  L21980071943.1  L22941438733.1  L24023900370.0  L24511873114.78 L25187853190.13 L25188864540.1  L25194140199.80 L27729706458.133L29021187662.2  L29738741675.1  L30439224333.1  L30812569823.153L33695720729.163L33985112333.1  L36316927438.2  L39269760500.1  L40226756952.1  L42411609006.0  L43055154860.74 L43495095303.1  L47230721790.120L48117620902.121L48117620911.69 L48127071455.163L5070094960.125 L51038230838.134L53063525639.1  L53537894342.3  L54220523271.1  L54437681876.9  L55351494680.12 L57355539152.120L5777911226.170 L57781587882.170L58790154276.12 L58970213517.1  L59272923917.1  L59308634497.13 L59351324120.1  L59578101107.145L60932203161.12 L61185983239.1  L62018535662.1  L62371012871.1  L63405906047.1  L64850595401.0  L65276887195.120L6912107244.120 L7040749983.79  L7715476710.76  L7738195705.2   L8707557133.1   L8855678079.1   L9356559645.13  L9717231777.0   P29008688568.158P29008688568.168P36312780344.158P36312780344.168P7750690063.158 P7750690063.168 Q10533598597.81 Q10592318623.166Q10592386206.146Q1453766547.167 Q1530342990.110 Q15474519600.154Q16178749883.146Q16798098773.154Q19135999377.164Q19312801942.168Q23802932279.164Q23937998252.81 Q24425655863.164Q25745664922.165Q25927363639.164Q26240822583.164Q26273198564.168Q26275478500.167Q26314584654.170Q26316671538.155Q27663034013.164Q31157884125.158Q31166267425.154Q31654203575.164Q32440833928.145Q32873557852.164Q33751454657.161Q33945187125.160Q34347029405.159Q34669208222.165Q35653441506.69 Q36477868772.157Q36480143588.158Q3848968118.161 Q39285966489.164Q40141998428.164Q40271359350.110Q40798937759.160Q44298944140.155Q44301027056.170Q44773262483.167Q45759487830.155Q46427498713.158Q47228431932.170Q47241206720.81 Q48117620904.146Q48117823211.158Q48117823211.168Q48119910507.170Q48132302231.145Q48234175664.167Q49242479227.161Q49698585326.156Q49698585326.166Q50922042716.164Q51682470940.161Q51740073116.163Q52194567059.167Q52744951088.157Q52747231024.158Q52747231024.168Q53580790879.167Q54487832473.159Q55026446744.163Q5596578838.170 Q55966432854.165Q56531220660.146Q58204958491.166Q58962872287.167Q58972088541.167Q59288651999.167Q59310664043.145Q59310664043.81 Q59321150548.146Q59321350679.158Q59321350679.168Q60109315147.69 Q60763208083.167Q60790458079.167Q61409249503.167Q6192914196.108 Q62012212072.110Q62022254708.81 Q62595035648.164Q64228675114.169Q65046345564.164Q65266402725.145Q65276887195.147Q67140767733.154Q67435635091.167Q68486783068.164Q6897428434.145 Q6912043747.167 Q6912107244.147 Q9122634134.158 Q9356560156.91  00000100V00W00m01L01M01N01d01e02<02=02P03503Z04?04L04d05:05;05Q05U05V05W06706O06e06i06m07107207Y07Z07[07\08208308708;08Q08g08k08l09009509609\09`09n0:X0;B0;X0<80<R0<V0<b0<f0=I0=Y0=Z0=[0>T0?30?80?<0?F0?K0?f0?g0?k0?n0@20@70@80@C0@N0@i0A40A50A90A>0B10B20C30D40E50F60Fo0Gh0H50HQ0H\0I60II0IT0I_0Ij0J50J60J70JS0JT0K00K;0K<0KV0L00LR0Lb0M>0MZ0Me0Mf0Mg0N20NR0ON0P00PL0Pk0QE0Q_0R[0S70SB0SR0T<0TL0Tn0UH0UY0V50V[0Vi0WS0XO0YK0ZM0[70[80[90[M0[a0[l0\V0]20]L0]f0^@0^Z0^[0_O0_k0_l0`=0`>0`Z0`[0a70aQ0aR0aS0aT0aU0aV0ag0bA0bB0bC0bO0bY0bc0bd0c[0cf0d10d<0dG0da0dl0e70eS0e^0e_0f3FS2LF2sp3LFB3sp13H152FB2HB5Ha_st5Hl_stFS2LF2sp3LFB3sp13H152FBS1R3HIA2LF2sp3LFB3sp13H152h12FBFFS2LF2sp3LFB3sp13H152FBFS2LF2sp3LFB3sp13H133H15FS1R3HIA1h2LF2sp3LFBS2LF2sp3LFB3sp13H152FB2HB5Ha_st5Hl_stS2LF2sp3LFB3sp13H152FB2HB5Ha_st5Hl_stS2LF2sp3LFB3sp13H152FB2HB5Ha_st5Hl_stS1R2LF2sp3LFBS1R2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H152FBFS2LF2sp3LFB3sp13H152FBS2FBSSS2LF2sp3LFB3SPR3sp13H152FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1S2LF2sp3LFB3sp13H152FBS2FBS2spS2FBSS2LF2sp3SPA3LFB3SPR3sp13H113H123H133H15FFFS2LF2sp3LFB3sp13H152FBFS2FBS2FBS2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H152FBS2FBFS2FBS3sp1SS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB3SPRS2FBS1R2LF3LFB3ALOS1R3NS12LF2sp2lo4STKk3LOS4STK03SLO3LFB3ALOS1R3NS12LF2sp2lo4STKk3LOS4STK03SLO3LFB3ALOS2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3SPR3sp13H152FB2F02F8S2LF2sp3LFB3sp13H133H152FBS2FBS2sp3sp13SP1S2FBS1R3NS12sp2lo4STKk4STK03SLO3sp13SP1S1R3ACV2FB2F02F1FFS1R2LF2sp3LFB3sp13H152FB2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS1R2sp2lo4STKk4STK03SLO3sp13SP1S3sp1S2FBS2FB2F02KbS3sp1S2LF2sp3LFB3sp13H152FB1c2HcSS2FBS1RS2FBS3sp1SS2LF3LFB2FBS2LF3LFB2FBS2LF2sp3LFB3SPR3sp13H113H15S2LF2sp3LFBFS2FBS3sp1S1R3NS12sp2lo4STKk3LOS4STK03SLO3ALO3ACV3SPR3sp13SP1SS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB3sp13SP12FB4FBLO2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB3sp13SP12FB4FBLO2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB3sp13SP12FB4FBLO2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB3sp13SP12FB4FBLO2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB2FB4FBLO2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB2FB4FBLO2HB5Ha_st5Hl_stS1R2LF2sp3LFBS1R2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FBS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF2sp3LFB3sp13H13S2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFFS1R3HIA1h2LF2sp3TOP3LFB4HTOPFS1R2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FBFS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2HB5Ha_st5Hl_stS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HB5Ha_st5Hl_stS1R2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FBFFS2LF3LFB2FBS1R2LF3LFB3sp12FB2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB3sp13SP12FB2HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB2FB2HB5Ha_st5Hl_stS1R2LF3LFB2FB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2lo3TOP3LFB4HTOPS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB3sp13SP12FB2HB5Ha_st5Hl_stS1R2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FBS1R3HIA1h2LF3LFBS1R2LF2sp2lo3LFB3sp13H132FB2HB5Ha_st5Hl_stS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2F02HBS1R2LF3LFB2FB2HB5Ha_st5Hl_stS1R2LF3LFB3ALO2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB3ALOS1R3NS12LF2sp2lo4STKk3LOS4STK03SLO3LFB3ALOS1R3NS12LF2sp2lo4STKk3LOS4STK03SLO3LFB3ALO2FB2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk3LOS4STK03SLO3LFB3ALO2FB2HB5Ha_st5Hl_stS1R3NS12LF2sp2lo4STKk3LOS4STK03SLO3LFB3ALO2FB2HB5Ha_st5Hl_st5SAEstS1R3NS12LF2sp2lo4STKk3LOS4STK03SLO3LFB3ALOFFS2LF3LFB2FB2HB5Ha_stS2LF3LFB2FB2HB5Ha_stS2LF3LFB2FBS1R2LF2sp2lo3LFB3sp13H132FB2HB5Ha_st5Hl_stS1R2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2HB5Ha_st5Hl_stFS1R3NS12LF2sp2lo4STKk4STK03SLO3LFB2FB2HB5Ha_st5Hl_stS1R2LF3LFB2FB2HB5Ha_st5Hl_stFS2LF3LFB2FB2F02HBFS1R2LF3LFB2FB2HB5Ha_st5Hl_stFS1R2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FB2HB5Ha_st5Hl_stFFFFFS1R2LF2lo3LOS3LFBS2LF3LFB2FB2HB5Ha_st5Hl_stFFS2LF3LFB3sp1S1R2LF3LFBS1R2LF3LFBFS1R2LF2sp3LFB3SPR3sp13H152FB2F02F82HB5Ha_st5Hl_st5SAEstS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FBFS2LF3LFB3sp13H143H15". (* [comment removed for export] *)
  #[using="LFB TPV SPA TOP SLO STK0 LOS STKk NS1 SM2 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_A ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(17.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2<.$4.Vm,Vlo,(15.&40.Vsp,))P,(2=.$4.Vm,)(31.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)$32.(:.(;.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.VPKA,)R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(<.&40.$33.)Vfc,(11.(5.&40.))Vm,(12.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST MI.
  unfold A_PK_PARSE_SUBPUBKEY.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  carve_frame 160%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0x531fc] [] 442%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1' end.
      destruct (stk_split asegs m1' lo sp1 (bv_unsigned sp + -160) ST ltac:(first [ clear - SP1 SLO STK0 NS1; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340476) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1' |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 192); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLO SP1 TOP NS1 STK0; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1' ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _).
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 2) with 256 in *. change (8 * 2 ^ 2) with 32 in FSH. change (Z.to_nat 256) with 256%nat in FRM. change (Z.to_nat 32) with 32%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -160) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 56) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STa SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 56) 8 STa ltac:(clear; lia)) as [STa' [jslot48 SLOT48]].
      replace (sp1 + 56 - Z.of_nat 8) with (sp1 + 48) in STa', SLOT48 by (clear; lia). clear STa.
      destruct (stk_split asegs m3 sp1 (sp1 + 32) (sp1 + 48) STa' ltac:(clear; lia)) as [STb STmid]. clear STa'.
      destruct (stk_carve asegs m3 sp1 (sp1 + 32) 24 STb ltac:(clear; lia)) as [STlo [jslots SLOTS]].
      replace (sp1 + 32 - Z.of_nat 24) with (sp1 + 8) in STlo, SLOTS by (clear; lia). clear STb.
      cb_all SLOT48.
      apply (rw_cells_split_CB asegs m3 (sp1 + 8) [] 24 jslots [] [8; 8; 8]%nat) in SLOTS; [| reflexivity]. cbn [mk_CB_cells app] in SLOTS. cb_all SLOTS.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [8; 8; 8; 232]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FREST.
      cb_all FHD.
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0xb02b4] [] 442%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  (* [comment removed for export] *)
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FRx : rw_cells _ mx (FB + 24) [CB 232 ?jr] |- _ =>
          apply (rw_cells_split_CB asegs mx (FB + 24) [] 232 jr [] [8; 8; 8; 16; 8; 24; 24; 40; 4; 4; 8; 4; 4; 64; 8]%nat) in FRx; [| reflexivity];
          cbn [mk_CB_cells app] in FRx;
          chunk_split FRx 1%nat FLNK FRMb;
          chunk_split FRMb 2%nat LPKC FRMc; chunk_split FRMc 1%nat J48 FRMd;
          chunk_split FRMd 1%nat LLEN FRMe; chunk_split FRMe 1%nat J72 FRMf;
          chunk_split FRMf 1%nat LPAR FRMg; chunk_split FRMg 1%nat J120 FRMh;
          chunk_split FRMh 2%nat LALG FRMi; chunk_split FRMi 1%nat J168 FRMj;
          chunk_split FRMj 2%nat LGID FRMk; chunk_split FRMk 1%nat J184 FFLAG;
          clear FLNK J48 J72 J120 J168 J184 FFLAG end end.
      lazymatch type of LPKC with rw_cells _ _ ?a _ => replace a with (FB + 32) in LPKC by (clear; lia) end.
      lazymatch type of LLEN with rw_cells _ _ ?a _ => replace a with (FB + 64) in LLEN by (clear; lia) end.
      lazymatch type of LPAR with rw_cells _ _ ?a _ => replace a with (FB + 96) in LPAR by (clear; lia) end.
      lazymatch type of LALG with rw_cells _ _ ?a _ => replace a with (FB + 160) in LALG by (clear; lia) end.
      lazymatch type of LGID with rw_cells _ _ ?a _ => replace a with (FB + 176) in LGID by (clear; lia) end.
      cb_all LPKC. cb_all LLEN. cb_all LALG. cb_all LGID.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end.
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      do 14 eexists. do 3 eexists. do 8 eexists. eexists.
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact LPKC|]. split; [exact LLEN|]. split; [exact LPAR|]. split; [exact LALG|]. split; [exact LGID|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOTS|]. split; [exact SLOT48|]. split; [exact STlo|]. split; [exact STmid|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|].
      exact PRES.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkPKA.

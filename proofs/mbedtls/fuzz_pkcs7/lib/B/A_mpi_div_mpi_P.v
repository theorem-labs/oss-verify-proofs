(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_div_stmtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAEcpSums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P004099ec7420c398 0 6 0 1 36 1 37 1 38 1 46 1 47 1P009f886894031602 0 4 0 1 63 1 64 1 65 1P0173524c59621c98 1 1 16 3 0 1 85 1 86 1 8 42 4 67 4 74 4 75 4 76 4 84 4 87 4 88 64P01e459cee4295819 0 3 0 1 48 1 62 1P023946bc008fe2e8 0 5 0 1 36 1 38 1 46 1 47 1P0339d3e4ebfb3faf 0 3 0 1 48 1 62 1P03b83079f1944e99 0 4 0 1 34 1 46 1 47 1P0462d5349a30c417 1 1 16 3 0 1 86 1 87 1 8 43 4 68 4 75 4 76 4 77 4 85 4 88 4 89 64P04832ec06d49c78a 0 6 0 1 36 1 37 1 38 1 46 1 47 1P05be0bdd50a1057c 0 6 0 1 36 1 37 1 38 1 46 1 47 1P05f311e96b54da8d 0 3 0 1 48 1 62 1P08c293e6e0fbefff 0 6 0 1 36 1 37 1 38 1 46 1 47 1P09d5437ce05791bf 0 5 0 1 36 1 38 1 46 1 47 1P0cb24c71a4e1756c 0 4 0 1 51 1 52 1 53 1P0d647e4ff2ba5c73 0 4 0 1 63 1 64 1 65 1P0dd2ec0ba34e496c 0 4 0 1 34 1 46 1 47 1P0e413f2027fbf9c1 0 4 0 1 34 1 46 1 47 1P0ec92890ac9aec40 0 4 0 1 63 1 64 1 65 1P10e358ca73ee9985 0 3 0 1 48 1 62 1P112cc904b36270a1 0 4 0 1 63 1 64 1 65 1P12b704e74b1ebf02 0 4 0 1 34 1 46 1 47 1P12d19e5c1e46232a 0 6 0 1 36 1 37 1 38 1 46 1 47 1P12d5ed06828ac6e0 0 5 0 1 36 1 38 1 46 1 47 1P13ade86d77d8d117 0 3 0 1 27 1 39 1P14696ec9d1a8b4f7 0 4 0 1 34 1 46 1 47 1P14b470575bdfa6b6 0 4 0 1 63 1 64 1 65 1P14f810666f87a49a 0 5 0 1 36 1 38 1 46 1 47 1P15c58f001d8c59db 0 4 0 1 34 1 46 1 47 1P171a9ee503ca68e6 1 1 64 2 1 1 56 1 3 0 1 57 1 58 64P178b0014a939e3e7 0 5 0 1 36 1 38 1 46 1 47 1P17ccbd437f3da509 1 2 32 3 0 1 84 1 87 1 32 8 42 1 59 1 67 1 74 1 75 1 76 1 85 1 86 1 2 88 1 89 1P17e8966f04fb0b4d 0 5 0 1 74 1 76 1 84 1 85 1P184603165a6fe8fd 1 1 16 2 0 1 46 1 3 4 1 47 1 48 16P19104c713148dc33 0 5 0 1 36 1 38 1 46 1 47 1P192720e75a58b0cd 0 3 0 1 48 1 62 1P194a3941a73b30b5 0 6 0 1 59 1 74 1 76 1 84 1 85 1P1994ee4c309b0ed1 0 4 0 1 34 1 46 1 47 1P1a138b8b1d9e702f 0 6 0 1 36 1 37 1 38 1 46 1 47 1P1baadbef24874c3a 0 5 0 1 36 1 38 1 46 1 47 1P1c131e9cd7a088a0 1 1 16 2 22 1 46 1 3 0 1 47 1 48 16P1c41a6c2855e3134 1 1 64 2 0 1 56 1 3 2 1 57 1 58 64P1d379ce6c2f1ddde 1 1 16 3 0 1 85 1 86 1 4 62 1 84 1 87 1 88 16P1db4b138c15420c1 0 4 0 1 34 1 46 1 47 1P1ede875da76d88f6 0 3 0 1 48 1 62 1P1f1b3094ffe1d6bf 0 6 0 1 36 1 37 1 38 1 46 1 47 1P1fd9c8dd7654d631 0 4 0 1 34 1 46 1 47 1P209eeb327da43ebf 0 6 0 1 36 1 37 1 38 1 46 1 47 1P20d3dac4c3d8e0ac 0 4 0 1 63 1 64 1 65 1P2102732e436f4b25 1 2 32 3 0 1 85 1 88 1 32 8 43 1 60 1 68 1 75 1 76 1 77 1 86 1 87 1 2 89 1 90 1P219a764ea0c1b15e 0 5 0 1 36 1 38 1 46 1 47 1P2219ddff95d138a6 0 5 0 1 36 1 38 1 46 1 47 1P22dde0bc64263f03 0 3 0 1 40 1 48 1P2326d64b83d4a8e3 0 4 0 1 34 1 46 1 47 1P2356f49515e51761 0 4 0 1 63 1 64 1 65 1P23ff9cfdc26c9ed4 0 4 0 1 63 1 64 1 65 1P244c253fb7b7338b 1 1 64 2 13 1 84 1 3 0 1 85 1 86 64P24d3fdb847b3ebd9 0 4 0 1 63 1 64 1 65 1P24e21c1686764215 0 3 0 1 48 1 62 1P27377b66e11436c6 0 4 0 1 34 1 46 1 47 1P275ca6170f0a648b 0 6 0 1 36 1 37 1 38 1 46 1 47 1P285045fcd2b72bbc 0 3 0 1 48 1 62 1P2b5107649c23c398 0 5 0 1 36 1 38 1 46 1 47 1P2b724c00a4eda99d 1 2 32 3 0 1 85 1 88 1 32 8 43 1 60 1 68 1 75 1 76 1 77 1 86 1 87 1 2 89 1 90 1P2b72d86b45a87ac9 0 3 0 1 48 1 62 1P2c13186d98f8a467 0 3 0 1 48 1 62 1P2d20dfbb9f03fcff 0 5 0 1 36 1 38 1 46 1 47 1P302b9b3394be33d0 0 5 0 1 36 1 38 1 46 1 47 1P30e360754dcba10c 1 1 64 2 42 1 57 1 3 0 1 56 1 58 64P319c524b0ec9bee3 0 4 0 1 34 1 46 1 47 1P32a3b51edfca8bcd 0 2 0 1 26 1P32d0bc0f9744e192 0 6 0 1 36 1 37 1 38 1 46 1 47 1P34018d0a96305a07 0 3 0 1 63 1 65 1P3533fd2cb0e4a6a8 0 4 0 1 63 1 64 1 65 1P353f017428f921d7 0 8 0 1 42 1 46 1 52 1 53 1 54 1 57 1 58 1P36391afc7453cf94 1 1 16 3 0 1 86 1 87 1 8 43 4 68 4 75 4 76 4 77 4 85 4 88 4 89 64P365c4369414efb01 1 2 32 3 0 1 85 1 88 1 32 8 43 1 60 1 68 1 75 1 76 1 77 1 86 1 87 1 2 89 1 90 1P36a7ff26d93b92dd 0 6 0 1 36 1 37 1 38 1 46 1 47 1P370e993e7a3554e0 0 3 0 1 36 1 50 1P3710e013bba28623 0 4 0 1 63 1 64 1 65 1P394aee68ff06fa02 0 5 0 1 36 1 38 1 46 1 47 1P3af61a3972853113 0 3 0 1 48 1 62 1P3b7f4b28e3f720b7 0 2 0 1 25 1P3bb5599c15179167 0 3 0 1 48 1 62 1P3bd095caeba214a9 1 1 16 3 0 1 86 1 87 1 8 43 4 68 4 75 4 76 4 77 4 85 4 88 4 89 64P3be3a3e8ce32189a 1 1 64 2 0 1 84 1 3 6 1 85 1 86 64P3c09802921ea14ac 0 4 0 1 63 1 64 1 65 1P3d176bbad1ab39ca 0 4 0 1 34 1 46 1 47 1P3d25c69236c0eb50 0 4 0 1 34 1 46 1 47 1P3d9704e62164bef8 0 6 0 1 36 1 37 1 38 1 46 1 47 1P3e1122f64683606a 0 5 0 1 36 1 38 1 46 1 47 1P3e44f36c27368f5e 0 6 0 1 36 1 37 1 38 1 46 1 47 1P3e93f9204a27806c 0 6 0 1 36 1 37 1 38 1 46 1 47 1P3eb1c22afd3a062a 0 3 0 1 48 1 62 1P3f0a28c51a1931ac 0 4 0 1 63 1 64 1 65 1N018b795efc34cf08N02ab80de5383061dN03257eca7cfd8d53N044eec6dbe1d8966N04cef959af3b3500N0582366f49f34ce4N065c1ba0b1958891N075be8eaf7657860N091fd954a54679f7N0fb72c2670845ea7N0fbac8b3682be922N114b2b4bb86a5a3fN121cd68b8a5eefccN125c9ea9ebfd38bdN1322b3634c0b6045N13a2117c6073ad56N141604e16c05c79fN15e8611f94316ac3N1688fdc5b1ed41abN16f9377aa224ebd3N173c82785294ef09N191693712b66377aN1922366ccd5b6fb1N19a0c198bef1450dN19cc3068efc9b30fN1a2174625faf9bccN1a6100cfaf718309N1ae12e8a1dfa9521N1afadfcd03193957N1bccbe0c0e8fafa6N1c69acb7633176e1N1e5929daf5fa84faN1f243d46da16f148N1fef7ddce78aec37N2069ab2f004220d3N20ac15797aa66253N21b573957692f5e1N22aceee19634915cN22ce370b24ea3236N2342f9ea389a810bN263667368de96062N26ee37251f082b7dN2791e57fe55574efN281bbe9f14797c27N293c7524744c401eN29d25bade06abe70N2a7e3aef6b20270bN2b165f624b1d8d07N2bf27eb8682c21f4N2d5f26e76db97b53N2d86b16fc86a0bcaN2dc6c3c1fff8cd59N2e09e9f3e9fc9eebN33953cc8c06a8b32N33cf59b36fb79440N348564c70b30917cN35a616dbcae4df8cN35d3b474b4a5801bN3671b2fcd48639dfN38d3c3af93794fdaN38e0cfc4af0dd74fN3aff5a623bc3c635"%lxh.
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
Ltac2 gd_tbl_A_mpi_div_mpi_P () : Init.string Init.list := ["Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.zcells"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "DV_FSH"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkD.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.A_MPI_DIV_MPI_E"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "WalkD.Call.EPOST"; "DV_FSH0"].


Definition A_UAR_GOT_DV : Z := 0x0f5ea8.           (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition DV_FSH : list cell := ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_P ()) "(0.$1.(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?8.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?8.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?8.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+4.))(2.$1.(3.(4.&8.+?3.))(2.$1.(3.(4.&8.+?3.))(2.$1.(3.(4.&8.+?3.))(2.$1.(3.(4.&8.+?3.))(5.$1.)))))))))))))))))))))))))))))(6.#4.))")
(* [comment removed for export] *).
Definition DV_FSH0 : list cell := ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_P ()) "(0.$1.(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?1.))(2.$1.(3.(4.&8.+?8.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?8.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+4.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.+?2.))(2.$1.(3.(4.&8.=))(2.$1.(3.(4.&8.+4.))(2.$1.(3.(4.&8.+?3.))(2.$1.(3.(4.&8.+?3.))(2.$1.(3.(4.&8.+?3.))(2.$1.(3.(4.&8.+?3.))(5.$1.)))))))))))))))))))))))))))))(6.#4.))").

Section WalkD.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_DV.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_DV.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (X A B lo : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - MPI_DIV_MPI_STACK_A - arl_need_rt R.
  Hypothesis SLOS : lo <= bv_unsigned sp - 352 - arl_need_smalloc R.
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
    unfold A_UAR_GOT_DV in UARG; unfold A_SMALLOC_2_DV in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_P ()) "Lms,$7.(8.$9.LFB,$9.(8.$9.Lsp1,$9.(8.(:.$;.VR,VHIA,)Lh1,(:.$;.VR,VHIA,)(8.P,(<.&40.)(=.(<.&8.))Lm1,P,(<.&40.)(=.(<.&8.))(8.(<.&40.)Lxra,(<.&40.)(8.(<.&40.)Lt0,(<.&40.)(8.(<.&40.)Lt1,(<.&40.)(8.(<.&40.)Lt2,(<.&40.)(8.(<.&40.)La1,(<.&40.)(8.(<.&40.)La3,(<.&40.)(8.(<.&40.)La4,(<.&40.)(8.(<.&40.)La5,(<.&40.)(8.(<.&40.)La6,(<.&40.)(8.(<.&40.)La7,(<.&40.)(8.(<.&40.)Lt3,(<.&40.)(8.(<.&40.)Lt4,(<.&40.)(8.(<.&40.)Lt5,(<.&40.)(8.(<.&40.)Lt6,(<.&40.)(8.(<.&40.)Lw0,(<.&40.)(8.(<.&40.)Lw1,(<.&40.)(8.(<.&40.)Lw2,(<.&40.)(8.(>.(<.&8.))Lj1,(>.(<.&8.))(8.(>.(<.&8.))Lj2,(>.(<.&8.))(8.(>.(<.&8.))Ljz,(>.(<.&8.))(8.(>.(<.&8.))Ljx,(>.(<.&8.))(8.(>.(<.&8.))Ljy,(>.(<.&8.))(8.(>.(<.&8.))Ljt,(>.(<.&8.))(8.(>.(<.&8.))Ljp,(>.(<.&8.))(8.(>.(<.&8.))Ljq,(>.(<.&8.))(8.(>.(<.&40.))Lsl,(>.(<.&40.))(8.(>.(<.&40.))Lsl2,(>.(<.&40.))(?.(10.$7.R20.(11.(12.R1;.(4.&40.R1>.)Vgp,Vtp,R1:.R19.R18.Vsp,(4.&40.R1>.)(4.&40.(13.R1?.+40.))R17.(4.&40.+10001.)R16.R15.R14.R13.R12.(4.&40.R1?.)(4.&40.R1?.)(4.&40.VX,)(4.&40.-8.)Vs6,Vs7,(4.&40.VA,)(4.&40.(13.(14.R1?.+3.)(15.(16.VR,))))(4.&40.VB,)(4.&40.(15.(16.VR,)))R11.R10.R?.R>.)VF,(4.&40.+9?614.)Vfc,(17.(<.&40.))R1<.(18.$;.)))(?.(?.(19.(1:.(1;.&40.Vsp,)+150.)R1>.)(19.R1>.(1:.(1;.&40.Vsp,)+140.)))(?.(10.$9.(1<.R1>.+20.)=)(?.(1=.$;.VR,VHIA,R1=.VLB,(2.(1>.$9.$9.)(1?.$9.$9.R1?.+100.)VLF,)R1<.)(?.(10.P,$9.Sp(20.$;.VR,VHIA,R1=.)(20.$;.VR,VHIA,Vh,))(?.(10.$9.(21.$;.VR,VHIA,R1=.)(21.$;.VR,VHIA,Vh,))(?.(10.$9.(22.$;.VR,VHIA,R1=.)(22.$;.VR,VHIA,Vh,))(?.(10.$9.(23.$;.VR,VHIA,R1=.)(23.$;.VR,VHIA,Vh,))(?.(10.$9.(24.$;.VR,VHIA,R1=.)(24.$;.VR,VHIA,Vh,))(?.(10.$9.(25.$;.VR,VHIA,R1=.)(25.$;.VR,VHIA,Vh,))(?.Pmo,$26.(27.(28.$;.VR,VHIA,R1>.R1.)(28.$;.VR,VHIA,Vh,R1.))(?.(10.$9.(1<.R1?.+40.)=)(?.(29.VR,VLB,VLF,R1?.+100.)(?.(2:.$;.R1<.R1?.(2.$1.(2;.R=.)(2.$1.(2;.R<.)(2.$1.(2;.R;.)(5.$1.)))))(?.(2:.$;.R1<.(13.R1?.+20.)(2.$1.(2<.#8.R:.)(5.$1.)))(?.(2:.$;.R1<.(13.R1?.+30.)(2.$1.(2<.#8.R9.)(5.$1.)))(?.(2:.$;.R1<.(13.R1?.+40.)(2.$1.(2<.#8.R8.)(5.$1.)))(?.(2:.$;.R1<.(13.R1?.+50.)(2.$1.(2<.#10.R7.)(5.$1.)))(?.(2:.$;.R1<.(13.R1?.+70.)(2.$1.(2<.#10.R6.)(5.$1.)))(?.(2:.$;.R1<.(13.R1?.+90.)(2.$1.(2<.#10.R5.)(5.$1.)))(?.(2:.$;.R1<.(13.R1?.+;0.)(2.$1.(2<.#<.R4.)(2.$1.(2<.#4.R3.)(5.$1.))))(?.(2:.$;.R1<.(13.(14.R1?.+3.)(15.(16.VR,)))$41.)(?.(2:.$;.R1<.(13.(1;.&40.Vsp,)-68.)(2.$1.(2;.Vs11,)(2.$1.(2;.Vs10,)(2.$1.(2;.Vs9,)(2.$1.(2;.Vs8,)(2.$1.(2;.Vs7,)(2.$1.(2;.Vs6,)(2.$1.(2;.Vs5,)(2.$1.(2;.Vs4,)(2.$1.(2;.Vs3,)(2.$1.(2;.Vs2,)(2.$1.(2;.Vs1,)(2.$1.(2;.Vs0,)(2.$1.(2;.Vra,)(5.$1.)))))))))))))))(?.(2:.$;.R1<.R1>.(2>.(<.&40.)$1.$2;.R2.))(?.(10.$2?.(30.(<.&40.)R2.)#13.)(?.(2:.$;.R1<.(13.R1>.+98.)(2.$1.(2;.(4.&40.=))(2.$1.(2;.(4.&40.R1?.))(5.$1.))))(?.(2:.$;.R1<.(13.R1>.+:8.)(2>.(<.&40.)$1.$2;.R1.))(?.(10.$2?.(30.(<.&40.)R1.)#6.)(?.(31.$;.R1<.(13.R1>.+=8.)(13.(1;.&40.Vsp,)-68.))(?.(31.$;.R1<.Vlo,R1>.)(?.(32.$;.R1<.)(33.$;.VR,VHIA,Vh,VLB,VLF,(1;.&40.Vsp,)(34.VR,)(5.$35.)Vm,R1<.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac cb8_all H :=
    repeat (lazymatch type of H with
            | rw_cells ?sg ?mx ?A ?cs =>
                let rec go pre rest :=
                  lazymatch rest with
                  | CB 8 ?bs :: ?post => apply (rw_cells_CB8_C8 sg mx A pre bs post) in H; cbn [app] in H
                  | ?c :: ?post => go (pre ++ [c]) post
                  end in go (@nil cell) cs
            end).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01<0@D18607476203.121D18607476203.123D23466511658.124D2457697676.153 D32458983511.153D32604263317.154D3386269608.152 D45702641177.152D50254960491.122D50254960491.124D560335984.78   D57174487360.153D62011770190.154D62012280210.78 D68409558507.152D6897506286.152 L12190320647.1  L14055515366.74 L18021517688.10 L18103702228.7  L19546883925.138L19980016842.10 L23466492214.145L27715613016.1  L27843863047.1  L29738741675.1  L33485826452.1  L33485826452.11 L34453352390.3  L39263166881.0  L40241890778.144L43055154860.72 L43495095303.1  L4666075286.1   L47230721790.134L48117620902.135L48117620911.73 L48132302231.90 L5070094960.138 L55351494680.11 L55810919039.21 L57355539152.131L58790154276.10 L59308634497.12 L59578101107.157L62018535662.1  L62821685255.1  L64850595401.0  L65276887195.134L6912107244.134 L7755433625.10  L9356559645.11  Q10533598597.80 Q10592386206.158Q1530342990.124 Q16178749883.158Q23937998252.80 Q32440833928.157Q35653441506.67 Q40271359350.124Q47241206720.80 Q48117620904.158Q48132302231.157Q56531220660.158Q59310664043.157Q59310664043.80 Q59321150548.158Q60109315147.67 Q6192914196.120 Q62012212072.124Q62022254708.80 Q65266402725.157Q65276887195.159Q6897428434.157 Q6912107244.159 Q9356560156.105 00000100200D00E00W01201301E01F01G01Z01l02@02M02N02`02d02o03003J03f04>04S04X04\04`04a04b04n04o05A05_05c05h06606X07:07\08=08M09309409J09T09k09n0:20:30:>0:I0:J0;50;B0;M0;_0;j0<F0<G0<f0=60=D0=f0>H0>I0>J0>K0>L0>]0>i0?30?=0?H0?S0?^0?i0@:FFS2LF2sp3LFB3sp12H7FS2LF2sp3LFB3sp12FBS1R3HIA2LF2sp3LFB3sp12h12FBFS2LF2sp3LFB3sp12FBFFS1R3HIA1h2LF2sp3LFBS2LF2sp3LFB3sp12FBS1R2LF2sp3LFB3sp12FBS1R2LF2sp3LFBFS2LF2sp3LFB3sp12FBS2FBS2LF2sp3LFBSS1R3NS12sp2lo4SLOS3sp13SP1S2LF2sp3LFB3SPR3sp12FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1S2LF2sp3LFB3sp12H72FBS3sp1S2FBS2FBFFS2sp3sp13SP1SS2LF2sp3LFB3sp12FBS1R5NEEDR2LF2sp2lo3SLO3LFB3SPRS2FBS3sp1S1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS2LF2sp3LFB3SPR3sp14SP1R2FB2F02F8S1R3ACV2FB2F02F1S2sp2r03SPA3sp11r4SP1M2H62H71q1H2q02H4FS1R2sp2lo4SLOS3sp13SP1S2FB2F02KbS2LF2sp3LFB3sp12FB1c2HcS1RS2spSS2LF3LFB2FBS2LF3LFB2FBSS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S1R2LF2sp3LFBS2LF3LFB2FBS2LF2sp3LFB3sp12H7S2LF3LFB2FBS1R3HIA1h2LF2sp3TOP3LFB4HTOPFS1R3HIA1h2LF2sp2lo3TOP3LFB4HTOPS1R3HIA1h2LF3LFBS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOFFFFS1R2LF2lo3LOS3LFBS2LF3LFB3sp1S1R2LF3LFBS1R2LF3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB3sp14SP1R". (* [comment removed for export] *)
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_P ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)P,(1=.$;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(31.$;.Vm,Vlo,(1;.&40.Vsp,))P,(32.$;.Vm,)P,(?.(19.=(13.VB,+:.))(36.(13.VB,+:.)(37.+2.+40.)))(38.$;.(16.VR,)(20.$;.VR,VHIA,Vh,)$39.(11.(12.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(4.&40.=)(4.&40.VX,)(4.&40.VA,)(4.&40.VB,)R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(4.&40.$3:.)Vfc,(17.(<.&40.))Vm,(18.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH ST MI BRG. unfold A_MPI_DIV_MPI_E. rt_facts.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
    destruct IMG' as (EGOT & ELO & EHI).
    (* [comment removed for export] *)
    zstep. carve_frame 320%nat ST.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose (lxi := lxA_img (arl_AL R) IMG).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9f4d0] [] 60%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    lx_carry.
    lx_align32 sp1.
    match goal with Hm : sp1 mod 32 = 0 |- _ => rename Hm into SP1M end.
    assert (SP1 : bv_unsigned sp - 336 <= sp1 <= bv_unsigned sp - 320)
      by (match goal with H1 : 0 <= sp1 + _, H2 : 0 <= - sp1 + _ |- _ => clear - H1 H2 SP1M SPA SPR end; Z.div_mod_to_equations; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    try match goal with H : stk _ _ lo (bv_unsigned sp + -320) |- _ => rename H into ST end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
    lazymatch goal with FRx : rw_cells _ mA (bv_unsigned sp + -320) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
    replace (bv_unsigned sp + -320 + 216) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
    destruct (stk_split asegs mA lo sp1 (bv_unsigned sp + -320) ST ltac:(clear - SP1 SLOS NS1; lia)) as [ST1 STx]. clear ST.
    release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ.
    destruct (stk_split asegs mA sp1 (sp1 + 216) (bv_unsigned sp + -104) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
    destruct (stk_carve asegs mA sp1 (sp1 + 216) 216 STlo ltac:(clear; lia)) as [STlo' [jslot SPILL]].
    replace (sp1 + 216 - Z.of_nat 216) with sp1 in STlo', SPILL by (clear; lia). clear STlo STlo'.
    apply (rw_cells_split_CB asegs mA sp1 [] 216 jslot [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in SPILL; [| reflexivity].
    cbn [mk_CB_cells app] in SPILL. cb8_all SPILL.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
        pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
        destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
        pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
      end end.
    rewrite EGOT in GOT. rewrite UARG in UGOT.
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x531fc] [] 80%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    replace (Z_to_bv 64 340476) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
    lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
    callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 224); rewrite ?(unsigned_lit sp1) by exact SP1R;
                first [ exact HHc | exact LFB | reflexivity | exact TPV | exact LOS | exact ST1
                | clear - SLOS SP1 TOP NS1; lia
                | clear; lia
                | assumption | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
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
    zstep. zstep.
    zstep. if_cases Kb; zify_cond Kb.
    2:{ exfalso. destruct FRSH as (F0 & F1 & _).
        try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
        rewrite ?Z.mod_small in Kb by (clear - F0 F1 ALO ACV LOS SLO SPR; lia). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
    clear Kb.
    change (64 * 2 ^ 2) with 256 in *. change (8 * 2 ^ 2) with 32 in FSH. change (Z.to_nat 256) with 256%nat in FRM. change (Z.to_nat 32) with 32%nat in FSH.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    destruct (frame_factsA R HIA CS h1 LB LF m3 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS. change (256 - 40) with 216 in IND.
    pose proof (art_stk_high asegs R HIA) as STKH.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 16; 16; 16; 16; 16; 16; 12; 4; 64]%nat) in FRM; [| reflexivity].
    cbn [mk_CB_cells app] in FRM.
    chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat J1C FRM3. chunk_split FRM3 1%nat RZ1 FRM4. chunk_split FRM4 1%nat J2C FRM5.
    chunk_split FRM5 1%nat RZ2 FRM6. chunk_split FRM6 1%nat JZC FRM7. chunk_split FRM7 1%nat RZ3 FRM8. chunk_split FRM8 1%nat XC FRM9. chunk_split FRM9 1%nat RZ4 FRM10.
    chunk_split FRM10 1%nat YC FRM11. chunk_split FRM11 1%nat RZ5 FRM12. chunk_split FRM12 1%nat TC FRM13. chunk_split FRM13 1%nat RZ6 FRM14. chunk_split FRM14 2%nat TPC FREST.
    lazymatch type of J1C with rw_cells _ _ ?a _ => replace a with (FB + 32) in J1C by (clear; lia) end.
    lazymatch type of J2C with rw_cells _ _ ?a _ => replace a with (FB + 48) in J2C by (clear; lia) end.
    lazymatch type of JZC with rw_cells _ _ ?a _ => replace a with (FB + 64) in JZC by (clear; lia) end.
    lazymatch type of XC with rw_cells _ _ ?a _ => replace a with (FB + 80) in XC by (clear; lia) end.
    lazymatch type of YC with rw_cells _ _ ?a _ => replace a with (FB + 112) in YC by (clear; lia) end.
    lazymatch type of TC with rw_cells _ _ ?a _ => replace a with (FB + 144) in TC by (clear; lia) end.
    lazymatch type of TPC with rw_cells _ _ ?a _ => replace a with (FB + 176) in TPC by (clear; lia) end.
    clear FLNK FREST RZ1 RZ2 RZ3 RZ4 RZ5 RZ6.
    cb8_to_c8 FHD (@nil cell).
    cbn [zcells] in FSH.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [652820] [] 120%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end.
    rewrite ?(Z.mod_small (B + 10)) by exact BRG.
    apply evtA_done. unfold S1P.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
    do 14 eexists. do 3 eexists. do 8 eexists.
    chunk_split SPILL 19%nat SPLA SPLB. chunk_split SPLB 2%nat SPLQ SPLC.
    lazymatch type of SPLC with rw_cells _ _ ?a _ => replace a with (sp1 + 168) in SPLC by (clear; lia) end.
    lazymatch type of SPLA with rw_cells _ _ _ ?cs =>
      let ws := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) cs) in exists ws end.
    lazymatch type of SPLC with rw_cells _ _ _ ?cs =>
      let ws := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) cs) in exists ws end.
    split; [reflexivity|].
    split; [exact SP1|]. split; [exact SP1M|].
    split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
    split; [exact F64|]. split; [exact FRSH|].
    split; [exact FHD|]. split; [exact J1C|]. split; [exact J2C|]. split; [exact JZC|]. split; [exact XC|]. split; [exact YC|]. split; [exact TC|]. split; [exact TPC|].
    split; [exact FSHX|].
    split; [exact SAVE|]. split; [exact SPLA|]. split; [reflexivity|]. split; [exact SPLQ|]. split; [exact SPLC|]. split; [reflexivity|]. split; [exact SThi|].
    split; [assumption|]. split; [assumption|].
    exact PRES.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_P ()) "Lms,$7.(8.P,(<.&40.)(=.(<.&8.))Lm',P,(<.&40.)(=.(<.&8.))(8.(:.$;.VR,VHIA,)Lh4,(:.$;.VR,VHIA,)(8.(<.&40.)Lt0,(<.&40.)(8.(<.&40.)Lt1,(<.&40.)(8.(<.&40.)Lt2,(<.&40.)(8.(<.&40.)La1,(<.&40.)(8.(<.&40.)La2,(<.&40.)(8.(<.&40.)La3,(<.&40.)(8.(<.&40.)La4,(<.&40.)(8.(<.&40.)La5,(<.&40.)(8.(<.&40.)La6,(<.&40.)(8.(<.&40.)La7,(<.&40.)(8.(<.&40.)Lt3,(<.&40.)(8.(<.&40.)Lt4,(<.&40.)(8.(<.&40.)Lt5,(<.&40.)(8.(<.&40.)Lt6,(<.&40.)(?.(10.$7.R11.(11.(12.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(4.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(3;.Vra,)Vfc,(17.(<.&40.))R10.(18.$;.)))(?.(32.$;.R10.)(?.(31.$;.R10.Vlo,(1;.&40.Vsp,))(?.(33.$;.VR,VHIA,O8.O7.VLF,(1;.&40.Vsp,)(34.VR,)O3.O5.R10.)(?.(33.$;.VR,VHIA,O8.O6.VLF,(1;.&40.Vsp,)(34.VR,)O2.O4.R10.)(?.(10.P,$9.Sp(20.$;.VR,VHIA,R?.)(20.$;.VR,VHIA,O8.))(?.(10.$9.(21.$;.VR,VHIA,R?.)(21.$;.VR,VHIA,O8.))(?.(10.$9.(22.$;.VR,VHIA,R?.)(22.$;.VR,VHIA,O8.))(?.(10.$9.(23.$;.VR,VHIA,R?.)(23.$;.VR,VHIA,O8.))(?.(10.$9.(24.$;.VR,VHIA,R?.)(24.$;.VR,VHIA,O8.))(?.(10.$9.(25.$;.VR,VHIA,R?.)(25.$;.VR,VHIA,O8.))(?.Pmo,$26.(27.(28.$;.VR,VHIA,R10.R1.)(28.$;.VR,VHIA,O8.R1.))(1=.$;.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 SPA; try lx_pin1 SLOS; try lx_pin1 NS1; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01H0@D2459732108.162 D2459793318.137 D32452690557.137D3376374386.136 D3386269615.162 D38320100953.162D43016287773.138D45717900227.136D62011770188.138D62022316111.162D66251787523.137D68407932977.136D6911601204.136 L17832996913.165L19546883927.124L19546883930.128L24876536089.160L2527391206.1   L30443457480.6  L35655538631.9  L39844638933.0  L41486840212.2  L42411609006.0  L47798928558.141L47801036031.141L48117620903.126L48117620904.122L48132302223.142L48132302231.141L48911768491.1  L5070094962.124 L5070094975.128 L50790580594.6  L59578101107.141L60098763854.3  L62018535662.1  L64850595401.0  L65276887188.125L65276887193.121L6899380056.1   L6912107235.125 L6912107246.121 L9356559676.11  P41479713552.164Q10592386204.142Q10592386207.146Q12191695080.164Q12191695088.165Q16178749881.142Q16178749882.146Q22358563588.145Q25138220955.162Q30132769282.165Q30147450662.143Q31314676345.141Q34796740410.146Q39028748170.162Q4125667684.161 Q4279611329.163 Q48117620905.146Q48117620906.142Q48132302223.145Q48132302231.141Q49293189221.143Q49293189224.147Q49307870529.165Q49307870553.164Q5935758158.163 Q59666529497.164Q59668625896.147Q60382659730.147Q60382659743.143Q60397339043.164Q60397339067.165Q64133651577.162Q65266402725.141Q65266402749.145Q65276887188.147Q65276887193.143Q67397950268.142Q6897428426.145 Q6897428434.141 Q6912107235.147 Q6912107246.143 Q7902384038.164 Q7902384062.165 Q7917062807.147 Q7917062810.143 00000100200A00B00C00[01301B01S01d02302402C02D02Y02n03B03F03]04604704804904:04;04]05?05a06C06G06a07;07R07f08008308408?08J08N08Y08d09O09P09[09f09g09h0:30:>0:?0:O0:P0:Q0:R0:S0:c0;00;=0;_0<A0<c0=E0=F0=G0=H0=I0=V0=W0=X0=Y0=Z0=[0=\0=i0>40>?0>J0>U0>V0>a0>l0?70?B0?V0?j0@>0@RFFS2LF3LFB2FB3sp1FFS1R3HIA2LF3LFB2FB3sp12h4S1R3HIA2LF3LFB2h32FB3sp1S2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1S2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1FS2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp11p2PBS2FBS1R5NEEDR2sp2lo3LOS3SLOS1R3HIA1h2sp2lo3TOP5HTOP3SFSFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS2FBS2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp14SP1R2F82F0S1R5NEEDR2sp2lo3LOS3SLOS2LF3LFB2FB3sp11c2HcS1R2lo3LOSS1RSS2LF3LFB2FBS2LF3LFB2FBS2FBS2LF3LFB2FBS2LF3LFB2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS2LF3LFB2FBS2LF3LFB2FBFFS2LF3LFB2FBS2LF3LFB2FBFS2LF3LFB2FB1p2PBFFFFS2LF3LFB2FB1p2PBS2LF3LFB1p2PBS2LF3LFB1p2PBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOFFFFS2LF3LFB1p2PBFFFFFFS2LF3LFB1p2PBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1". (* [comment removed for export] *)
  #[using="LFB TOP SLO LOS NEEDR IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_P ()) "Ph3,(:.$;.VR,VHIA,)PLBa,(>.$3<.)PLBb,(>.$3<.)Pm0,P,(<.&40.)(=.(<.&8.))Pm2x,P,(<.&40.)(=.(<.&8.))Pmm,P,(<.&40.)(=.(<.&8.))PWA,(>.$35.)PWB,(>.$35.)PFB,$9.Psp1,$9.Pxra,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Pa0v,(<.&40.)Ps4v,(<.&40.)Ps6v,(<.&40.)Ps7v,(<.&40.)Ps8v,(<.&40.)Ps10v,(<.&40.)Pw0,(<.&40.)Pw1,(<.&40.)Pw2,(<.&40.)Pr,$9.P,(1=.$;.VR,VHIA,R23.R21.(2.(1>.$9.$9.)(1?.$9.$9.R1;.+100.)VLF,)R1>.)P,Px,$9.P,(20.$;.VR,VHIA,Vh,R1.)(20.$;.VR,VHIA,R26.R2.)P,(10.$9.(21.$;.VR,VHIA,R25.)(21.$;.VR,VHIA,Vh,))P,(10.$9.(22.$;.VR,VHIA,R26.)(22.$;.VR,VHIA,Vh,))P,(?.(19.(1:.(1;.&40.Vsp,)+150.)R1>.)(19.R1>.(1:.(1;.&40.Vsp,)+140.)))P,(10.$9.(1<.R1?.+20.)=)P,(10.$9.(1<.R21.+40.)=)P,(29.VR,R29.VLF,R22.+100.)P,(29.VR,R29.VLF,R23.+100.)P,(3=.(20.$;.VR,VHIA,Vh,)R24.+100.)P,PB,$9.Pj,$9.P,(3>.(1>.$9.$9.)(1?.$9.$9.R2.R1.)VLF,)(3?.(19.(13.R28.+100.)R3.)(19.(13.R3.R2.)R28.))P,Pb',$3<.P,(3>.$3<.R1.R2>.)(3>.$3<.R2.R2>.)P,(2:.$;.R2:.R27.(2.$1.(2;.R10.)(2.$1.(2;.R?.)(2.$1.(2;.R>.)(5.$1.)))))P,(2:.$;.R2;.(13.(14.R28.+3.)(15.(16.VR,)))$2=.)P,(2:.$;.R2<.(13.(1;.&40.Vsp,)-68.)(2.$1.(2;.Vs11,)(2.$1.(2;.Vs10,)(2.$1.(2;.Vs9,)(2.$1.(2;.Vs8,)(2.$1.(2;.Vs7,)(2.$1.(2;.Vs6,)(2.$1.(2;.Vs5,)(2.$1.(2;.Vs4,)(2.$1.(2;.Vs3,)(2.$1.(2;.Vs2,)(2.$1.(2;.Vs1,)(2.$1.(2;.Vs0,)(2.$1.(2;.Vra,)(5.$1.)))))))))))))))P,(31.$;.R2=.Vlo,(13.(1;.&40.Vsp,)-68.))P,(32.$;.R2>.)P,(33.$;.VR,VHIA,R34.R33.VLF,(1;.&40.Vsp,)(34.VR,)R2>.R31.R2?.)P,(33.$;.VR,VHIA,R35.R33.VLF,(1;.&40.Vsp,)(34.VR,)R2>.R31.R30.)(38.$;.(16.VR,)(20.$;.VR,VHIA,R36.)(40.R36.R35.R34.R33.R32.R30.R2?.R14.)(11.(12.R2<.(4.&40.R2=.)Vgp,Vtp,R2;.R2:.R29.Vsp,(4.&40.R2=.)R1=.R28.R27.R26.R25.R24.R23.R22.(4.&40.R2>.)(4.&40.R2>.)R1<.(4.&40.-8.)R1;.R1:.R19.(4.&40.(13.(14.R2>.+3.)(15.(16.VR,))))R18.(4.&40.R14.)R21.R20.R1?.R1>.)VF,(4.&40.+9?93<.)Vfc,(17.(<.&40.))R31.(18.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE STlo MI PRES PRES2. unfold DV_FSH in FSH. cbn [app zcells] in FSH.
    rt_facts.
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3. rewrite ET3, ES3 in HTOP3.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    assert (CFB3 : crange (hcs asegs R HIA h3) FB 256) by (eapply crange_mono; [exact HCS3| exact CFB]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR TOP HTOP3; lia]).
    assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
    assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 256 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
    (* [comment removed for export] *)
    pose (lxi := lxA_img (arl_AL R) IMG).
    assert (SFF : shadow_free R LBa LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 256)
      by (eapply shadow_free_fresh; [exact FRSH | exact (proj2 (proj2 (proj2 PRES))) | clear; lia | clear; lia | exact ALO | exact AP]).
    assert (SFF2 : shadow_free R LBb LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 256)
      by (eapply shadow_free_fresh; [exact FRSH3 | exact (proj2 (proj2 (proj2 PRES2))) | clear; lia | clear; lia | exact ALO | exact AP]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [653808] [] 80%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    (* [comment removed for export] *)
    match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
    destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 256) :: LF) me FB 256 HHe ltac:(left; reflexivity))
      as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
    replace (FB + 256 - 8) with (FB + 248) in ROp by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp. clear Hold.
    assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 256) :: LF))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right].
      eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
    assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 256) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
    assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS NEEDR; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| clear - LOS SLO NEEDR; lia]).
    assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| clear - LOS SLO NEEDR; lia]).
    clear HHe NCp NSp FHD.
    repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H | H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
    zstep. zstep.
    fake_free_done p HSp.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [] 60%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    cbn [lb_remove fst Z.eqb] in HM4. rewrite Z.eqb_refl in HM4.
    apply evtA_done. unfold EPOST.
    exists mf, h4. do 14 eexists.
    split; [reflexivity|].
    split; [assumption|].
    split; [assumption|].   (* [comment removed for export] *)
    split; [exact PRES|]. split; [exact PRES2|].
    split; [rewrite E4cs; reflexivity|]. split; [exact E4top|]. split; [exact E4stk|]. split; [exact E4flag|]. split; [exact E4vol|]. split; [exact E4fr|].
    split; [exact HKI4|]. exact HM4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.
End WalkD.

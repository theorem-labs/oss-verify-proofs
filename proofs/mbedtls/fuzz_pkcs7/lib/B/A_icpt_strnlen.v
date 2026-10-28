(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip A_amem_lib A_icpt_read.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA Restrict RestrictLib RestrictRun SRz SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Hoare MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_memchr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_icpt_str.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0026e152ba8b5394 0 2 0 1 47 1P00358a7d363e6b7d 0 3 1 1 48 1 49 1P00998a524e56ecf5 0 2 0 1 47 1P00db90019218bcf9 0 3 1 1 48 1 49 1P02d3481fc14550b2 0 3 1 1 48 1 49 1P02defe05b480d595 0 3 1 1 48 1 49 1P03651dd3024751da 0 2 0 1 37 1P042cbfa657f23cf0 0 2 0 1 47 1P043b703d882288af 0 3 1 1 48 1 49 1P04b123e91bc6736a 0 3 1 1 48 1 49 1P04b66d6b0e7b40cf 0 3 1 1 48 1 49 1P04e44c1e9bbe3450 0 3 1 1 48 1 49 1P04e8241859be42c2 0 3 1 1 48 1 49 1P050441355364dc4d 0 2 0 1 47 1P05a817d3014adc4b 0 2 0 1 46 1P05f811581ef49a40 0 3 1 1 48 1 49 1P060f6249065bd7e7 0 3 1 1 48 1 49 1P061f8d31c1ec7aa5 0 3 1 1 48 1 49 1P066a940b6532a516 0 2 0 1 47 1P069d509c83d805ec 0 3 1 1 48 1 49 1P06af97cbae4e88a5 0 3 0 1 38 1 49 1P073c4db76104b470 0 3 1 1 48 1 49 1P077a079bd9899165 0 2 0 1 49 1P0784d9ca1bba538a 0 3 1 1 48 1 49 1P07ad93d3c2293853 0 2 0 1 38 1P07d470e61de6a393 0 3 1 1 48 1 49 1P0956fc2f4b15d398 0 3 1 1 48 1 49 1P097902ae94f6b2d5 0 2 0 1 44 1P09a97668a10364e2 0 2 0 1 47 1P0a92708075208216 0 3 1 1 48 1 49 1P0ad51668ebc3dc79 0 2 0 1 44 1P0b4e4c1d228c0829 0 2 0 1 47 1P0c37cfca1bafb95d 0 3 1 1 48 1 49 1P0c4ce8e56081ef88 0 3 0 1 38 1 49 1P0c6838343d725b16 0 2 0 1 47 1P0c9b615cd030722c 0 3 1 1 48 1 49 1P0d0bdb0eaa8ea329 0 2 0 1 26 1P0d39cc6f45e12872 0 2 0 1 37 1P0d564a226b899b27 0 3 1 1 48 1 49 1P0dbd13482dd4e1fa 0 2 0 1 47 1P0e1c1da72c22a7c6 0 2 0 1 47 1P0e35f3f6d657b7fe 0 3 1 1 48 1 49 1P0e49b0266575b673 0 3 1 1 48 1 49 1P0e986cbfe07fbde4 0 3 1 1 48 1 49 1P0f012ec4b8573a4a 0 3 1 1 48 1 49 1P0f1220bced2be27b 0 3 1 1 48 1 49 1P0fc3f50749f227a8 0 3 1 1 48 1 49 1P0fc56b68b471dad2 0 2 0 1 47 1P0fd4adc576c21784 0 3 1 1 48 1 49 1P1079d6bdf3ce4632 0 3 1 1 48 1 49 1P109a43c6ce810856 0 3 1 1 48 1 49 1P10eb4343bdbfa9ed 0 3 1 1 48 1 49 1P114aa505a6574b5b 0 3 1 1 48 1 49 1P11d94fe0b07ddadf 0 3 1 1 48 1 49 1P12b9aa009e25b200 0 2 0 1 47 1P130224dd455b28fa 0 3 1 1 48 1 49 1P13c151441479ca3f 0 3 1 1 48 1 49 1P13cbc24a97ed9fdc 0 3 1 1 48 1 49 1P13f4edc6b98e751f 0 3 1 1 48 1 49 1P14312e58da8bfe1b 0 3 1 1 48 1 49 1P14b27bf1c35c0097 0 2 0 1 47 1P14fa9998cae16af9 0 2 0 1 47 1P14fbf8450b256ecb 0 3 1 1 48 1 49 1P1521beda1a2bd2a3 0 3 1 1 48 1 49 1P15efcab3bab3e489 0 2 0 1 47 1P160ea82d84a17b8d 0 3 1 1 48 1 49 1P177903ea144c28f2 0 3 0 1 38 1 49 1P17825076c7389186 0 2 0 1 47 1P1797f28e67f12120 0 3 1 1 48 1 49 1P17f27a9ff478d510 0 2 0 1 47 1P182a43bef42de138 0 2 0 1 47 1P182fbec304bda774 0 2 0 1 44 1P18a56a166f8e6101 0 2 0 1 26 1P18e2f3e4fe043ec3 0 3 1 1 48 1 49 1P19fc04c59303af08 0 2 0 1 47 1P1a035b143f402466 0 2 0 1 47 1P1a7a3b870927df92 0 3 1 1 48 1 49 1P1ac3260050c44195 0 3 1 1 48 1 49 1P1b3b891d172e2a93 0 3 1 1 48 1 49 1P1c20139b5a573191 0 3 1 1 48 1 49 1P1c23ff40f08a1f1d 0 3 1 1 48 1 49 1P1c3bad4e7432e695 0 3 1 1 48 1 49 1P1d181259f1e8b9f0 0 2 0 1 44 1P1d2234bac802a49d 0 2 0 1 47 1P1d4a3250c1ea26c6 0 3 1 1 48 1 49 1P1d919bede4f234f2 0 2 0 1 47 1P1d99c2f22e1adf4d 0 3 1 1 48 1 49 1P1dccc0e1d12402db 0 3 1 1 48 1 49 1P1e431e219a88a551 0 3 1 1 48 1 49 1P1e89d58dd07c3360 0 2 0 1 26 1P1ee52b8557b5c005 0 3 1 1 48 1 49 1P1ef4679d117b8c24 0 2 0 1 47 1P1f6ae7d008758c93 0 3 1 1 48 1 49 1P1fa0fcc79d147d0c 0 2 0 1 44 1P2019c36c7013d5bf 0 2 0 1 44 1P204d47cc29ce4087 0 2 0 1 37 1P20ac66d579790a70 0 3 1 1 48 1 49 1P217be4d1da5acbca 0 3 1 1 48 1 49 1P21e6d09859af4c0e 0 3 1 1 48 1 49 1P22308ebd41213b87 0 2 0 1 26 1P22d0f65e75113217 0 2 0 1 47 1P22f3f0432e892e8a 0 2 0 1 47 1P23041a2d6da85ae2 0 2 0 1 47 1P230698f49280c613 0 2 0 1 26 1P23447c505d777c2a 0 3 1 1 48 1 49 1P237e4c866f857192 0 2 0 1 26 1P23b628b98b19fc40 0 2 0 1 47 1P24425e6b2616b8e2 0 3 0 1 47 1 49 1P250ea497f96cacc7 0 3 1 1 48 1 49 1P25861157dd6525e8 0 3 1 1 48 1 49 1P25a30a0a74e6c202 0 2 0 1 47 1P25c15df0bb48a4fc 0 3 1 1 48 1 49 1P25cd862c06104bf1 0 3 1 1 48 1 49 1P25d1f771c032bc4f 0 2 0 1 48 1P2685486b67fb8f96 0 3 1 1 48 1 49 1P26cd4358e0f3a3b1 0 2 0 1 47 1P27638aba2d6c2f25 0 3 1 1 48 1 49 1P27fde4d153fb6ab7 0 3 1 1 48 1 49 1P295a1184b8edc855 0 3 1 1 48 1 49 1P29ac0cf3b92cd9e1 0 3 1 1 48 1 49 1P29cdd040be87001c 0 3 1 1 48 1 49 1P29fb2e6f54425964 0 3 1 1 48 1 49 1P2a10c2ba1e7d473b 0 3 1 1 48 1 49 1P2a5fffa21cc32ff5 0 3 1 1 48 1 49 1P2a81d9a7ac4394ba 0 2 0 1 47 1P2aa57c5563404bdc 0 3 1 1 48 1 49 1P2ad138271aea0632 0 3 0 1 38 1 49 1P2adb9c3470e6d78b 0 3 1 1 48 1 49 1P2d3b59fd002337bf 0 2 0 1 47 1P2df2421cc9e38e78 0 3 1 1 48 1 49 1P2df263afba93b849 0 2 0 1 47 1P2df3672bb28e6824 0 2 0 1 47 1P2df61f46b54ccf6e 0 2 0 1 47 1P2e02e24251e6ce47 0 2 0 1 26 1P2ed6c3c74377d6dc 0 3 1 1 48 1 49 1P2f4af7641cb7b140 0 3 1 1 48 1 49 1P3006ae1d323706a0 0 3 1 1 48 1 49 1P304fef330719aead 0 2 0 1 44 1P3110bd49954b6ccf 0 3 1 1 48 1 49 1P318f58f806a23dc1 0 2 0 1 47 1P3191aa1985b4c921 0 3 1 1 48 1 49 1P3254797f23cd45c0 0 2 0 1 44 1P33443a115efaa38f 0 3 1 1 48 1 49 1P33e90a6e27a9e016 0 2 0 1 47 1P3498be4c57c41539 0 2 0 1 47 1P34b577be2693039f 0 3 1 1 48 1 49 1P34bb4a35a3bd1d87 0 2 0 1 26 1P355e279c296bdd44 0 2 0 1 47 1P35f7e3eb65dff358 0 3 1 1 48 1 49 1P36619fc1eee6f87f 0 3 1 1 48 1 49 1P369dcfd9a99ecac9 0 3 1 1 48 1 49 1P36fc8686c8e34e27 0 3 1 1 48 1 49 1P3784b3ee859afb58 0 2 0 1 44 1P379fba3498bc9dff 0 3 1 1 48 1 49 1P37d75e1b4a5065f2 0 2 0 1 47 1P37dde53cd1766313 0 3 1 1 48 1 49 1P37ef29dd859eb9a3 0 2 0 1 44 1P3891012e0f9d459e 0 3 1 1 48 1 49 1P39189b7a0c59edde 0 3 1 1 48 1 49 1P393b86109b9f5738 0 3 1 1 48 1 49 1P39de90ceab565775 0 3 1 1 48 1 49 1P3ae9e673bbf6aec0 0 2 0 1 26 1P3afdee4423a42d3e 0 2 0 1 48 1P3c5c6f94ddbdacb8 0 3 1 1 48 1 49 1P3c8bccd09d41bb9d 0 3 1 1 48 1 49 1P3dbb2c8a8f9cc1e0 0 3 1 1 48 1 49 1P3e254ba274e0e169 0 3 1 1 48 1 49 1P3e265772e83751f3 0 2 0 1 49 1P3e7e3d7731f5ee3c 0 3 1 1 48 1 49 1P3e991c15a92e4464 0 2 0 1 47 1P3ea37cea5357dfb6 0 2 0 1 26 1P3ebf0e4a0c904b5d 0 3 1 1 48 1 49 1P3ec1f5f1be708b6f 0 3 0 1 37 1 49 1P3f23e355e77177c8 0 3 1 1 48 1 49 1P3f75351167803139 0 2 0 1 47 1P3fc16f56866be69f 0 3 1 1 48 1 49 1N0834193ab23408d4N1bd26309a0aa6b73N2fbbad1b0c529e7cN321a5b32e8e1abd2N3b943075583362f2"%lxh.
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
Ltac2 gd_tbl_A_icpt_strnlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Walk.sn_consts"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.sn_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Walk.sn_back_post"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record sn_consts (m : mem) : Prop := {
    snc_inited : ro_cells asegs m 0x10a6d8 [C1 (Z_to_bv 8 1)];           (* [comment removed for export] *)
    snc_rstrnlen : ro_cells asegs m 0x0f7c78 [C8 (Z_to_bv 64 0x0eb24c)]; (* [comment removed for export] *)
    snc_rmemchr : ro_cells asegs m 0x0f7b90 [C8 (Z_to_bv 64 0x0ea8c4)];  (* [comment removed for export] *)
    snc_cf : ro_cells asegs m 0x0f5e40 [C8 (Z_to_bv 64 0x19b528)];       (* [comment removed for export] *)
    snc_flag : ro_cells asegs m 0x19b623 [C1 (Z_to_bv 8 1)];             (* [comment removed for export] *)
    snc_rip : rip_consts m
  }.

  Lemma sn_consts_munch : forall lo hi m m',
    munch [(lo, hi)] m m' -> HSE < lo -> sn_consts m -> sn_consts m'.
  Proof.
    intros lo hi m m' MU LO [R1 R2 R3 R4 R5 RC].
    split; [ .. | eapply rip_consts_munch; eauto];
      (eapply ro_cells_transport; [eassumption | exact MU | cbn; split; [lia | exact I]]).
  Qed.

  (* [comment removed for export] *)
  Definition sn_pre_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (ra s0 s1 s2 s3 : word) (P n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_strnlen ()) "Lms',$0.(1.(2.(3.&8.))Lj8,(2.(3.&8.))(1.(2.(3.&8.))Lj2080,(2.(3.&8.))(1.(2.(3.&8.))Lj2072,(2.(3.&8.))(1.P,(3.&40.)(4.(3.&8.))Lm',P,(3.&40.)(4.(3.&8.))(5.(6.$0.R5.(7.(8.(9.&40.+59?28.)(9.&40.(:.(;.&40.O21.)-10=0.))O20.O1?.O1>.O1=.O1<.(9.&40.(:.(;.&40.O21.)-880.))(9.&40.O3.)(9.&40.O4.)(9.&40.=)(9.&40.O3.)(9.&40.+>:8<4.)O1;.O1:.O19.O18.(9.&40.O4.)(9.&40.=)(9.&40.+1.)O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.)O;.(9.&40.+>:8<4.)O:.(<.(3.&40.))R1.(=.$>.)))(5.(?.(10.(11.$12.$12.)(13.$12.$12.O2.(;.&40.O21.))(14.(11.$12.$12.)))O1.R1.)(5.(15.$>.O1.R1.)(5.(16.$>.R1.)(5.(17.$>.R1.O2.(:.(;.&40.O21.)-10=0.))(5.(18.$>.R1.(:.(;.&40.O21.)-40.)(10.$19.(1:.O15.)(10.$19.(1:.O16.)(10.$19.(1:.O17.)(10.$19.(1:.O5.)(10.$19.(1:.O6.)(10.$19.(1:.O7.)(10.$19.(1:.O8.)(10.$19.(1:.O9.)(14.$19.))))))))))(5.(18.$>.R1.(:.(;.&40.O21.)-860.)(10.$19.(1;.#820.R3.)(14.$19.)))(5.(18.$>.R1.(:.(;.&40.O21.)-880.)(10.$19.(1;.#8.R4.)(10.$19.(1:.(9.&40.+1.))(10.$19.(1:.O21.)(10.$19.(1:.(9.&40.+58:64.))(14.$19.))))))(5.(18.$>.R1.(:.(;.&40.O21.)-8;8.)(10.$19.(1:.O16.)(10.$19.(1:.O17.)(10.$19.(1:.(9.&40.O3.))(10.$19.(1:.(9.&40.O4.))(10.$19.(1:.(9.&40.O4.))(10.$19.(1:.(9.&40.O3.))(10.$19.(1:.(9.&40.+>;270.))(14.$19.)))))))))(18.$>.R1.(:.(;.&40.O21.)-10=0.)(10.$19.(1;.#818.R2.)(14.$19.))))))))))))))))")
(* [comment removed for export] *).

  Lemma sn_pre : ltac2:(CDefT.buildp (gd_tbl_A_icpt_strnlen ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(1<.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(4.(3.&8.))PP,$12.Pn,$12.Plo,$12.P,(1=.R4.)P,(17.$>.R5.R2.(;.&40.R25.))P,(1>.+10007???7???.R3.)P,(1?.R4.(20.(;.&40.R27.)+1120.))P,(21.VCS,R5.(20.(;.&40.R28.)R5.))P,(16.$>.R9.)P,(5.(1?.=R9.)(1>.R9.(22.+2.+40.)))P,(5.(1?.=R9.)(1>.R9.(22.+2.+40.)))P,(6.(3.&40.)R24.(9.&40.R;.))P,(6.(3.&40.)R24.(9.&40.R;.))(23.$>.VAL,VCS,(24.R2>.R2=.R2<.R2;.R2:.R29.R22.R21.R20.R1?.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R2?.R28.R27.R1>.R1=.R=.R<.R;.R>.)(7.(8.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(9.&40.+586?4.)R?.(<.(3.&40.))R>.(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros RC ST LO0 SPL SCS MI P0 N0 -> ->. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    destruct RC as [RC1 RC2 RC3 RC4 RC5 RC].
    (* [comment removed for export] *)
    assert (GSB0 : al_gsb AL = 0x1099f8) by (destruct IMG' as (_ & _ & _ & G); exact G). clear GSB.
    change (lx_hidden (al_sb AL = SB)) in ASB.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. carve_frame 2080%nat ST. carve_frame 32%nat ST. carve_frame 56%nat ST. carve_frame 2072%nat ST. carve_frame 16%nat ST.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x0ea8c4] [] 200%N). lx_tree.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ ?mx (bv_unsigned sp + -4320) _, ST0 : stk _ ?mx lo _ |- _ =>
      chunk_split H 2%nat FRt Hr1; chunk_split Hr1 1%nat FRe Hr2; chunk_split Hr2 7%nat FRd Hr3; chunk_split Hr3 4%nat FRc Hr4; chunk_split Hr4 1%nat FRb FRa;
      lazymatch type of FRe with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -4304) in FRe by (clear; lia) end;
      lazymatch type of FRd with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2232) in FRd by (clear; lia) end;
      lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2176) in FRc by (clear; lia) end;
      lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2144) in FRb by (clear; lia) end;
      lazymatch type of FRa with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -64) in FRa by (clear; lia) end;
      release_frame FRt ST0 (bv_unsigned sp + -4304)
    end.
    apply evtA_done; unfold sn_pre_post.
    lazymatch goal with
    | FRa : rw_cells _ ?mx (bv_unsigned sp + -64) _, FRb : rw_cells _ ?mx (bv_unsigned sp + -2144) [CB 2080 ?jb],
      FRc : rw_cells _ ?mx (bv_unsigned sp + -2176) (CB 8 ?jc :: _), FRd : rw_cells _ ?mx (bv_unsigned sp + -2232) _,
      FRe : rw_cells _ ?mx (bv_unsigned sp + -4304) [CB 2072 ?je], STx : stk _ ?mx lo _, MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx |- _ =>
      exists jc, jb, je, mx; split; [reflexivity|];
      split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact STx|];
      split; [exact FRa|]; split; [exact FRb|]; split; [exact FRc|]; split; [exact FRd| exact FRe]
    | |- ?g => idtac "NOMATCH"; match goal with H : ?T |- _ => idtac H ":" T; fail end
    end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition sn_back_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_strnlen ()) "Lms',$0.(1.(3.&40.)Lt0,(3.&40.)(1.(3.&40.)Lt1,(3.&40.)(1.(3.&40.)Lt2,(3.&40.)(1.(3.&40.)La1,(3.&40.)(1.(3.&40.)La2,(3.&40.)(1.(3.&40.)La3,(3.&40.)(1.(3.&40.)La4,(3.&40.)(1.(3.&40.)La5,(3.&40.)(1.(3.&40.)La6,(3.&40.)(1.(3.&40.)La7,(3.&40.)(1.(3.&40.)Lt3,(3.&40.)(1.(3.&40.)Lt4,(3.&40.)(1.(3.&40.)Lt5,(3.&40.)(1.(3.&40.)Lt6,(3.&40.)(1.P,(3.&40.)(4.(3.&8.))Lm',P,(3.&40.)(4.(3.&8.))(5.(6.$0.R10.(7.(8.O15.O14.O13.O12.R?.R>.R=.O11.O10.(9.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(25.O15.)O4.(<.(3.&40.))R1.(=.$>.)))(5.(?.(10.(11.$12.$12.)(13.$12.$12.O2.(;.&40.O14.))(14.(11.$12.$12.)))O1.R1.)(5.(15.$>.O1.R1.)(5.(16.$>.R1.)(17.$>.R1.O2.(;.&40.O14.)))))))))))))))))))))")
(* [comment removed for export] *).

  Lemma sn_back : ltac2:(CDefT.buildp (gd_tbl_A_icpt_strnlen ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Prax,(3.&40.)PF,(1<.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(4.(3.&8.))PP,$12.PL,$12.Pn,$12.Plo,$12.Pj8,(2.(3.&8.))Pj2080,(2.(3.&8.))Pj2072,(2.(3.&8.))P,(26.$>.VAL,VCS,R8.R7.(:.R6.+1.))P,(1?.=R7.)P,(1>.(:.R8.+1.)(22.+2.+28.))P,(1>.(:.R9.+1.)R8.)P,(1>.R9.(22.+2.+3?.))P,(27.R<.(:.(:.(:.R<.R;.)+1.)+7.))P,(21.VCS,(20.R=.(28.R=.+40.))+40.)P,(21.VCS,(20.(:.R>.R=.)(28.(:.R>.R=.)+40.))+40.)P,Pc,$12.P,A1.VCS,R1.(1.(3.&8.)Lb,(3.&8.)(29.$>.R13.(2:.VAL,R3.)(10.(3.&8.)R1.(14.(3.&8.)))))P,(1=.R11.)P,(17.$>.R12.R>.(:.(;.&40.R32.)-10=0.))P,(1>.+10007???7???.R?.)P,(1?.R10.(20.(;.&40.R34.)+1120.))P,(1>.(;.&40.R35.)(22.+2.+3?.))P,(21.VCS,R12.(20.(;.&40.R36.)R12.))P,(16.$>.R17.)P,(18.$>.R18.(:.(;.&40.R38.)-40.)(10.$19.(1:.R25.)(10.$19.(1:.R26.)(10.$19.(1:.R27.)(10.$19.(1:.R28.)(10.$19.(1:.R29.)(10.$19.(1:.R31.)(10.$19.(1:.R32.)(10.$19.(1:.R39.)(14.$19.))))))))))P,(18.$>.R19.(:.(;.&40.R39.)-860.)(10.$19.(1;.#820.R13.)(14.$19.)))P,(18.$>.R1:.(:.(;.&40.R3:.)-880.)(10.$19.(1;.#8.R15.)(10.$19.(1:.(9.&40.+1.))(10.$19.(1:.R3:.)(10.$19.(1:.(9.&40.+58:64.))(14.$19.))))))P,(18.$>.R1;.(:.(;.&40.R3;.)-8;8.)(10.$19.(1:.R29.)(10.$19.(1:.R2:.)(10.$19.(1:.(9.&40.R18.))(10.$19.(1:.(9.&40.R1:.))(10.$19.(1:.(9.&40.R1:.))(10.$19.(1:.(9.&40.R18.))(10.$19.(1:.(9.&40.+>;270.))(14.$19.)))))))))P,(18.$>.R1<.(:.(;.&40.R3<.)-10=0.)(10.$19.(1;.#818.R15.)(14.$19.)))(23.$>.VAL,VCS,(2;.R3>.R3=.R3<.R3;.R37.R36.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R1?.R1>.R1;.R19.R1=.)(7.(8.R20.(9.&40.(:.(;.&40.R3=.)-10=0.))R3<.R3;.R3:.R39.R38.(9.&40.(:.(;.&40.R3=.)-880.))(9.&40.R1:.)(9.&40.(:.R1<.R1;.))R35.R34.R33.R32.R31.R30.R2?.(9.&40.R1<.)(9.&40.=)(9.&40.+1.)R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R1?.(9.&40.+59?28.)R1>.(<.(3.&40.))R1=.(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until j2072. intros OBJ L0 N LN N63 AR HULL0 HULL1 SHRD RC ST LO0 SPL SPH SCS MI FRa FRb FRc FRd FRe. al_facts.
    pose proof AR as AR'. unfold app_range in AR'.
    assert (B0 : 0 < P /\ P + L + 1 + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RCC. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC].
    assert (GSB0 : al_gsb AL = 0x1099f8) by (destruct IMG' as (_ & _ & _ & G); exact G). clear GSB.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x59f40] [] 60%N). lx_tree.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx, WMx : wmono _ m mx |- _ =>
        try clear MU; try clear WM; clear FRa FRb FRc FRd FRe ST OBJ MI; rename MUx into MU; rename WMx into WM;
        pose proof (shrd_munch AL CS CSOK [(lo, bv_unsigned sp)] m mx ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil]) MU SHRD) as SH1;
        pose proof (rip_consts_munch _ _ m mx MU LO0 RC) as RCx1
      end end.
    callxA_sp (bv_unsigned sp + -4304) (eapply mc_chk with (P := P) (L := L) (lo := lo);
            rewrite ?(unsigned_lit (bv_unsigned sp + -4304)) by lia;
            first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact HULL0 | exact HULL1 | exact SH1 | exact RCx1 | exact AR
                  | eassumption | lia | eapply crange_sub; [exact SCS | lia | lia] ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "MC-LEFT:" g end.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x58a80] [] 80%N). lx_tree.
    (* [comment removed for export] *)
    try (lazymatch goal with E : ?mq = ?mp |- _ (MS _ _ _ _ _ ?mq _) => is_var mq; subst mq end).
    repeat match goal with H1 : ?T, H2 : ?T |- _ => lazymatch type of T with Prop => clear H2 end end.
    (* [comment removed for export] *)
    lazymatch goal with H1 : rw_cells _ ?mx (bv_unsigned sp + -4304) _, H : stk _ ?mx lo _ |- _ (MS _ _ _ _ _ ?mx _) => release_frame H1 H (bv_unsigned sp + -2232)%Z end.
    lazymatch goal with H1 : rw_cells _ ?mx (bv_unsigned sp + -2232) _, H : stk _ ?mx lo _ |- _ (MS _ _ _ _ _ ?mx _) => release_frame H1 H (bv_unsigned sp + -2176)%Z end.
    lazymatch goal with H1 : rw_cells _ ?mx (bv_unsigned sp + -2176) _, H : stk _ ?mx lo _ |- _ (MS _ _ _ _ _ ?mx _) => release_frame H1 H (bv_unsigned sp + -2144)%Z end.
    (* [comment removed for export] *)
    lazymatch goal with OBJx : aobj _ _ _ ?mx P _, MUx : munch _ m ?mx |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (shrd_munch AL CS CSOK [(lo, bv_unsigned sp)] m mx ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil]) MUx SHRD) as SH;
      pose proof (rip_consts_munch _ _ m mx MUx LO0 RC) as RCx;
      callxA_sp (bv_unsigned sp + -2144) (eapply sn_chk with (P := P) (L := L) (lo := lo);
            rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
            first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | exact HULL0 | exact HULL1 | exact SH | exact RCx | exact AR
                  | eassumption | lia | eapply crange_sub; [exact SCS | lia | lia] ])
    end.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SN-LEFT:" g end.
    (* [comment removed for export] *)
    lx_run_tac (PLAN ([] : list Z) [] 40%N). lx_tree.
    try (lazymatch goal with E : ?mq = ?mp |- _ (MS _ _ _ _ _ ?mq _) => is_var mq; subst mq end).
    unfold sn_back_post; finish.
  Qed.

End Walk.

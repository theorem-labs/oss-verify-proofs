(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_x509_seq_stmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_get_san_A A_x509_akid_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00fa917b59240fcd 0 3 0 1 83 1 84 1P01395449e52de7aa 0 2 0 1 62 1P02ced5f1d20870c6 0 2 0 1 60 1P03c2c4a284438b65 0 2 0 1 60 1P03f92cd69c3fe64f 0 2 0 1 62 1P06a74f53a44be2c1 0 7 0 1 84 1 87 1 95 1 96 1 101 1 102 1P07278abb70e5c3d4 0 2 0 1 63 1P07e45816924dcc4d 0 2 0 1 1 1P091afe827f0b914c 0 2 0 1 62 1P09229c49b3fa1665 0 2 0 1 61 1P0a844c5b8258a818 0 8 0 1 44 1 65 1 75 1 77 1 84 1 89 1 90 1P0aff9f9bcc0e7163 0 2 0 1 44 1P0d95f375c055df9a 0 2 0 1 45 1P0e5316e133615ad8 1 1 8 3 0 1 101 1 104 1 8 45 1 84 1 87 1 95 1 96 1 102 1 103 1 105 8P100dd5032f44a0ec 0 2 0 1 1 1P12937e8031391021 0 5 0 1 44 1 45 1 82 1 86 1P19d842c56fe666ba 0 4 0 8 17 8 100 8 101 8P1f6838e0411b484d 0 2 0 1 1 1P279e245b7725051e 0 4 0 1 45 1 82 1 86 1P2afdb9e3cd0009d7 0 7 0 1 84 1 87 1 95 1 96 1 101 1 102 1P2d1df2489e8f0e81 0 2 0 1 44 1P2dec1ad7aac856c8 0 2 0 1 1 1P2e4424ca80c1e77b 1 2 8 2 0 1 100 1 8 2 87 1 101 1 2 102 1 103 1P2e7388b1473a04aa 0 4 0 8 17 8 100 8 101 8P3135d3098910c789 1 1 8 3 0 1 101 1 104 1 8 45 1 84 1 93 1 95 1 96 1 102 1 103 1 105 8P33b600810c5d1fd4 0 2 0 1 62 1P3669c244600fd947 1 2 8 2 0 1 100 1 8 2 87 1 101 1 2 102 1 103 1P371e2a4cf16134ce 1 1 8 3 0 1 101 1 104 1 8 45 1 84 1 87 1 95 1 96 1 102 1 103 1 105 8P379a2b12e5066326 1 2 8 2 0 1 100 1 8 2 87 1 101 1 2 102 1 103 1P3883af0ddb32a1e0 1 1 8 3 0 1 101 1 104 1 8 45 1 84 1 87 1 95 1 96 1 102 1 103 1 105 8P38f2c9b5d31f3080 0 2 0 1 64 1P3a06eb498e74abf1 0 2 0 1 60 1P3a3bc3ca3689b6a2 0 4 0 8 17 8 100 8 101 8P3a91373e0766ce26 0 7 0 1 84 1 87 1 95 1 96 1 101 1 102 1P3bd83414d497252f 0 2 0 1 44 1P3d717dfd3c7a05e5 0 7 0 1 84 1 93 1 95 1 96 1 101 1 102 1N00215f4745f26d4aN00e910f8d490db8fN01e969f457b31b7bN0245b0c2f2fdc74aN0274ac9bf44ffa8aN02923ee0d73eb4dcN029956292a682653N02fa9abeadb20227N033943fa70a76de5N034fe2142d71c929N03548243f8c1b8f2N0367f158261ff83dN03698262bb65547bN06886c2c3af68cc5N06d9a68a6dbd3c1fN07132c48f2c36ccfN073fd2d23722c174N076129331c4cbd94N07785a7f092ef78dN07fa88f877654cacN0804562f28642040N08943d18c6e50159N08ac39d28e6ff080N08b4afd4103a4ed2N08f996c0ea20fab0N0936479c0c08f048N0939119a8fd6cddcN09fac14e7c04948fN0bee36b9cfc7e10eN0bee81a03d8b1f1eN0c3acf2b9d358079N0cccb071f0c65698N0cf04cb50129cb0bN0d1b2d127b0a8781N0d4ca78312f5ea0aN0d8491845e943884N0e0ea74ec4ea1553N0e35ae28f85b48cdN0ed60541a7c101b6N0ef74a0aa7f2b941N0f41c43a5544733dN0f78d25df233ca57N101a0903b8a9e41aN1054059809af0666N10b639a0ab62fae3N125e2a8e5b3be52fN1293d99f3a308983N12ea316dafaa10eeN133988d9ab1cc86cN1352e0a85e3d6f1dN138c018ac67963e2N1434d39ea0b746a6N146a1ceb2be4e510N14cde25a7598722cN1550173bc5376cc9N158fb05b3bc557b6N159558842f07fbd2N16225f34d6b99df7N16922b53007b96e7N16b54faf01853ad0N16ec52f3261d58deN16ece1bebebaa650N16fad7e64b2edfbcN175f61019249f901N17c8c297b81eaaf9N17dab3cffe1f2365N198c9360ee4eb67eN19a19426fbd76890N1bc04f3ee2641418N1bd83be69540e43dN1bea65607be787eaN1bed9a9d89d4721cN1cba550f83bd5d8cN1e34339a652dc3b5N1f23f7aa9ccd99ddN1f55725472b65a65N20011d378f1d0b7dN2080a80a309360ecN20fc8e28f1435ae4N213827d53cb509bfN217ce9c48f075ebdN2196451791a4ced2N21a33d1dc0353749N21e37908f656b7a2N22261d5895c54ecfN2239f9e7c721716cN22a802e8828297a3N22c3c49257e80d5cN24396dadc973901fN244d6d4d066e6b86N24d8cdb5c65148beN25295797c0203618N2593313d9057a955N25c6ebb83a00246aN26a611c0ceaaf1f4N26e41586287b44f8N27ea5360f3d07309N2821d496c7f1e2f3N2837d6929e2eb1ceN28cc89c29a6e997bN28e9c38c89267344N29b1bea78780d0a0N29d08b42c292dee0N2a28db082bd41684N2ac98629e2a7bbc5N2adb42e8a6296d1aN2b2ed8dbb25597f5N2bf7dbc702179292N2c43fedd02146d21N2cb7c707c9572488N2ccc740d2dcbc323N2d09b1460856c3c8N2d2d2590ffe4a3abN2ded3ac7543bc5a6N2e4c3d1edc9c07c4N2eb0c5c25f4a5598N2ed2a7d38d57bd30N2f3169612ca747d8N2fc57f77e812fee7N302d7303194337eaN3044d88807e0de85N30677e332d1f3873N309ba7f5af1335c8N30d720d7ab25f42dN31643c74d2ff247aN318f6b718d94f4a8N31b74ccdc6ceb648N323b755d59036b45N32d1d51d1829afaeN331e5cf8f62d7269N34233b72d8e8cd0aN342826f074f6b1f4N34a5048711a00f29N34b96733f22c1911N3558ad0d350fb744N35738ececa713309N357a6947ad109c4cN35c7617846ff64ecN361b3b7c7c989f97N36c921e846e03a2cN36f15e38a38eabc9N3744cf9342bc9474N3754c09bf64b8c94N3763b38bc73ed160N3783391333c9d6caN37b21ab5c766639cN38e1ac254245172aN391bc96ba3a47232N39deb3f41339dc4fN39fac668e2c0a39cN3a26009a1840985aN3a9be08db67a7478N3adbe4401b037685N3bcca65a8562632dN3c18e128b7ead446N3c6da21d7948ec7fN3e693587d214f324N3ee351e14916d4e0"%lxh.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_x509_akid_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.MID2P"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Walk.Call.EXQ3"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0G.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Variable STKe : Z.
  Hypothesis STKe0 : 0 <= STKe.

  Local Notation STKk := (A_x509_akid_A.STKk R STKe).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP AK P END BUF lo slo : Z) (bs : list byte) (ct cpad r1 r2 r3 r4 : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALA : AK mod 8 = 0.
  Hypothesis AK0 : 0 < AK.
  Hypothesis CWA : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) AK 80.
  Hypothesis AKLO : AK + 80 <= lo.
  Hypothesis DAB : AK + 80 <= BUF \/ BUF + n <= AK.
  Hypothesis D1 : PP + 8 <= AK \/ AK + 80 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKk.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L33981044001.1L7661493751.1 000004008S2AKS2AK". (* [comment removed for export] *)
  Let CWA0 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) AK 24.
  Proof. eapply client_wrange_inside; [exact CWA| intros b Hb; exact Hb| clear; lia| clear; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2666878454.1 L43776819202.1000004008S2AKS2AK". (* [comment removed for export] *)
  Let CWHD : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (AK + 24) 32.
  Proof. eapply client_wrange_inside; [exact CWA| intros b Hb; exact Hb| clear; lia| clear; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L35372053634.1L47309331446.1000004008S2AKS2AK". (* [comment removed for export] *)
  Let CWA56 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (AK + 56) 24.
  Proof. eapply client_wrange_inside; [exact CWA| intros b Hb; exact Hb| clear; lia| clear; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_0G in SM0; unfold A_x509_akid_A.STKk in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (AK, AK + 80)].
  Local Notation SAVEL := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHG := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation HEADC := (seq_cells ct cpad 0 0 0).
  Local Notation AK56C := [C4 r1; C4 r2; C8 r3; C8 r4].
  Local Notation EXQ := (A_x509_akid_A.EXQ R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP AK P END lo slo ct cpad r1 r2 r3 r4).

  (* [comment removed for export] *)
  Definition CALLQ (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_akid_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm3,P,(2.&40.)(3.(2.&8.))(1.$4.Lq,$4.(1.(2.&40.)Lw0,(2.&40.)(1.(2.&40.)Lw1,(2.&40.)(1.(2.&40.)Lw2,(2.&40.)(1.(2.&40.)LLw,(2.&40.)(1.(2.&40.)Lk1,(2.&40.)(1.(2.&40.)Lk2,(2.&40.)(1.(2.&40.)Lk3,(2.&40.)(1.(2.&40.)Lk4,(2.&40.)(1.(2.&40.)Lxra,(2.&40.)(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)Lx13,(2.&40.)(1.(2.&40.)Lx14,(2.&40.)(1.(2.&40.)Lx15,(2.&40.)(1.(2.&40.)Lx16,(2.&40.)(1.(2.&40.)Lx17,(2.&40.)(1.(2.&40.)Lx28,(2.&40.)(1.(2.&40.)Lx29,(2.&40.)(1.(2.&40.)Lx30,(2.&40.)(1.(2.&40.)Lx31,(2.&40.)(5.(6.$0.R18.(7.(8.R=.(9.&40.O2.)Vgp,Vtp,R<.R;.R:.Vsp,(9.&40.O2.)(9.&40.VPP,)(9.&40.(:.R16.(;.&40.R12.)))(9.&40.(:.VAK,+18.))R9.R8.R7.R6.R5.(9.&40.O3.)(9.&40.VPP,)(9.&40.VEND,)(9.&40.VAK,)(9.&40.(:.O3.+20.))(9.&40.O3.)(9.&40.(:.(<.O3.+3.)(=.(>.VR,))))(9.&40.(=.(>.VR,)))(9.&40.(:.(<.VPP,+3.)(=.(>.VR,))))Vs11,R4.R3.R2.R1.)VF,(9.&40.+:;88<.)Vfc,(?.(2.&40.))R17.(10.$11.)))(5.(12.VP,R16.)(5.(12.(:.R16.(;.&40.R12.))VEND,)(5.(13.$11.VR,VHIA,O1.VLB,(14.(15.$4.$4.)(16.$4.$4.O3.+40.)VLF,)R17.)(5.(17.$11.R17.)(5.(18.$11.R17.O3.(14.$19.(1:.R15.)(14.$19.(1:.R14.)(14.$19.(1:.R13.)(1;.$19.)))))(5.(18.$11.R17.(:.O3.+20.)(14.$19.(1:.R12.)(1;.$19.)))(5.(18.$11.R17.(:.(<.O3.+3.)(=.(>.VR,)))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.=))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(1;.$19.))))))))))(5.(18.$11.R17.(:.(;.&40.Vsp,)-60.)(14.$19.(1:.Vs10,)(14.$19.(1:.Vs9,)(14.$19.(1:.Vs8,)(14.$19.(1:.Vs7,)(14.$19.(1:.Vs6,)(14.$19.(1:.Vs5,)(14.$19.(1:.Vs4,)(14.$19.(1:.Vs3,)(14.$19.(1:.Vs2,)(14.$19.(1:.Vs1,)(14.$19.(1:.Vs0,)(14.$19.(1:.Vra,)(1;.$19.))))))))))))))(5.(18.$11.R17.(:.O2.+18.)(14.$19.(1:.(9.&40.O3.))(1;.$19.)))(5.(1=.$11.R17.(:.O2.+20.)(:.(;.&40.Vsp,)-60.))(5.(1=.$11.R17.O2.(:.O2.+18.))(5.(1=.$11.R17.Vlo,O2.)(5.(18.$11.R17.VPP,(14.$19.(1:.(9.&40.R16.))(1;.$19.)))(5.(18.$11.R17.VAK,(14.$19.(1>.R11.)(14.$19.(1>.R10.)(14.$19.(1:.R?.)(14.$19.(1:.R>.)(1;.$19.))))))(5.(18.$11.R17.(:.VAK,+18.)(1?.Vct,Vcpad,===))(5.(18.$11.R17.(:.VAK,+38.)(14.$19.(1>.Vr1,)(14.$19.(1>.Vr2,)(14.$19.(1:.Vr3,)(14.$19.(1:.Vr4,)(1;.$19.))))))(5.(20.$11.R17.VBUF,Vbs,)(5.(21.$11.(>.VR,)(22.$11.VR,VHIA,Vh,)R17.VPP,+8.)(5.(21.$11.(>.VR,)(22.$11.VR,VHIA,Vh,)R17.VAK,+50.)(5.(21.$11.(>.VR,)(22.$11.VR,VHIA,Vh,)R17.VBUF,(23.(24.(2.&8.)Vbs,)))(5.(25.$11.VR,VHIA,Vh,VLB,VLF,(;.&40.Vsp,)(;.&40.Vsp,)(14.(15.$4.$4.)(16.$4.$4.VPP,(:.VPP,+8.))(14.(15.$4.$4.)(16.$4.$4.VAK,(:.VAK,+50.))(1;.(15.$4.$4.))))Vm,R17.)(5.(26.$11.(>.VR,)R17.Vslo,O2.)(26.$11.(>.VR,)R17.O2.(;.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition MID2P (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := fun ms => EXQ FB sp1 h1 ms \/ CALLQ FB sp1 h1 ms.

  Ltac fold_head :=
    lazymatch goal with H : rw_cells _ ?mxc (AK + 24) _ |- _ => change (rw_cells asegs mxc (AK + 24) HEADC) in H end.
  Ltac fin_exq rv qv :=
    fold_head; apply evtA_done; left; unfold A_x509_akid_A.EXQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    exists rv, qv; repeat (lazymatch goal with |- ex _ => eexists end);
    split; [reflexivity|].
  Ltac fin_exq_e qv :=
    fold_head; apply evtA_done; left; unfold A_x509_akid_A.EXQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    eexists; exists qv; repeat (lazymatch goal with |- ex _ => eexists end);
    split; [reflexivity|].
  Ltac errsum RRg :=
      first [ rewrite A_x509_get_san_A.swrap32_errsum'' by (clear - RRg; lia)
            | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - RRg; lia))
            | match goal with |- ?g => idtac "ERRSUM-LEFT" end ].

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 CWA56; try lx_pin1 CWHD; try lx_pin1 CWA0; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 DAB; try lx_pin1 CWA; try lx_pin1 r4; try lx_pin1 r3; try lx_pin1 r2; try lx_pin1 r1; try lx_pin1 cpad; try lx_pin1 ct; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04B0@C40858145355.212C60410007123.211D10636937134.212D10637083017.165D12660624642.164D14196765253.165D14197109858.212D16071854214.212D2457516971.212 D2459793318.163 D31528442088.164D3162115617.212 D3162359814.165 D32452690557.163D32458870384.212D32604263317.166D33196749127.164D3376374386.162 D35869989040.162D36106837483.165D36107017164.212D39243574473.212D39258595524.163D39604305264.212D39604616023.165D45717900227.162D46794843979.212D46795284844.165D60109265000.165D60109446735.212D62011770190.166D64997949699.163D65008160014.212D68221095944.212D68407932977.162D6911601204.162 K18493193506.212K20981739667.210K24799944541.212K27175203321.212K29378133114.212K30993319891.212K34158808196.212K59453006468.212K65858155712.211K68239931741.212L10945075201.158L13977709985.0  L17605293694.139L17696450187.34 L17705907808.2  L18489062900.25 L18497025716.2  L19546883931.139L19698471166.34 L20115755706.6  L20977711877.2  L21654730866.2  L24206288344.1  L24812802884.2  L25850648867.34 L25850682667.154L25850682667.157L2621559066.1   L27111942217.1  L27162377696.2  L27206487025.3  L27380263923.3  L27821999381.186L27938633021.34 L28344346468.2  L29391009772.3  L30997223346.3  L31168734357.135L34171225874.2  L3484572308.34  L35236225328.25 L35653441506.11 L35903316071.25 L38235734261.1  L39166347177.7  L41110154015.25 L41251426164.1  L41359293650.2  L42612502460.154L43202358961.144L43305107741.25 L43809418676.185L4472687353.146 L45363093875.169L47870616696.2  L4809844382.2   L48117620900.136L48117620903.135L48132302231.169L48257107102.2  L48834180257.0  L49233373885.2  L5021251703.1   L50678314462.3  L51675925653.154L51675925653.157L52840517793.6  L53359885363.2  L54287022143.156L54287186364.155L55195235631.25 L55432526301.2  L56380991837.10 L56775192862.156L57387012359.34 L58972524609.3  L59308586248.2  L59308660947.3  L59309005265.156L59314873579.3  L59314873579.4  L59314988138.1  L59314988138.157L59333918210.7  L59448584466.2  L60098763854.6  L62275882349.3  L63344940145.2  L63506675754.156L63506675754.163L63506675754.192L63506774312.157L64179129035.1  L64482796004.3  L65862516566.2  L66812728480.3  L67070089790.2  L67556946858.2  L67922604617.0  L68244403524.2  L6912107234.135 L881835912.0    L9080220944.4   L9356559676.16  L9783143000.2   L9817154962.156 O11096106305.212O11640932009.211O14614127145.209O14912726833.209O19003878908.212O20866770946.212O21230138846.211O22525005962.211O2384783454.209 O31189574615.212O32135033303.212O3493317847.210 O37559489567.212O3821773283.212 O41068820901.212O424351700.210  O44938202843.210O45626564938.211O48557518091.212O48841645583.211O49539471840.212O49701823576.209O50011839873.210O55209884805.210O55240955659.212O56187274208.212O62594918972.211P21647862485.210P27200772438.209P28346987971.211P41371876950.211P47876372191.210P4804097081.212 P48262927929.212P49230739482.209P50671478649.210P53363783589.211P55446727546.211P62260666314.210P63339218646.211P64484389699.209P66818508295.212P67064334489.209P67551224077.212Q10523111604.172Q10588139941.186Q10592386206.170Q10592533181.212Q10636937134.212Q10637083020.171Q10651763882.175Q11133374175.212Q11657053839.212Q11657494700.170Q12551782730.171Q12562269300.210Q12658527489.177Q14851060500.179Q14851060501.180Q17027695041.212Q17157233336.176Q17681074618.212Q19551029871.186Q21767670690.212Q23218748859.170Q23219026840.212Q23925414038.178Q23927511197.172Q26028057496.211Q26030071964.212Q26032252593.183Q27573751300.212Q27942454161.212Q2803826605.212 Q29775981542.212Q31158247845.169Q31168734357.173Q31170831514.181Q32440833928.169Q32681607669.212Q32681887702.170Q32681887704.172Q33194651972.177Q33271078526.210Q33285757760.171Q33983176476.176Q3477426724.212 Q34964382778.212Q34966725143.183Q34979309374.211Q38250992816.180Q38250992817.179Q40216052035.169Q40259924710.186Q42437284302.212Q42439168719.212Q42441479395.185Q43336582017.171Q43351262911.210Q43878048877.179Q46794843979.212Q46795284841.171Q46805771343.175Q47230721777.172Q47313632828.210Q47328312066.171Q48117620904.170Q48118064779.212Q48132302231.169Q49563371193.172Q49886471361.211Q49888159685.212Q49890664936.183Q56525516080.169Q56530976407.212Q56531220660.170Q59865603600.212Q59867617340.185Q59871812881.212Q62009673038.178Q62011770181.172Q67517027822.210Q67523317968.171Q6897428434.169 Q6910010093.181 Q6912107234.173 Q8697078920.212 Q8699324297.212 Q8701272485.185 Q9356559674.189 Q9640321936.186 Q9644583048.212 00000400800M00b01;01<01=02A02B02C02D02E02F02[03003N03g03h03i03j03k03l03m03n03o04D04Y04n05L05j06A06V06k07h07i08>09;0:50:I0:]0;[0<10<n0=k0>e0?90?_0?`0@D0AX0A`0BO0BP0Bk0D30DI0DJ0DK0DP0DQ0Dl0EN0F00F50F90F:0F;0FF0F[0Ge0Gf0Gg0Gh0H60H70I<0J50JM0J\0J`0K80KG0KK0KL0Ka0L]0Lk0MN0N20NL0NM0NN0O<0Oj0PX0PY0PZ0P[0P\0P]0Q?0Qa0R70R80R90R:0Ri0Rj0SC0Tc0U40U@0UF0UQ0UR0US0UT0UW0UX0V00V10V;0V<0V=0V>0V?0V@0VA0VB0VC0VD0VE0VF0VG0VH0VI0VW0VX0Vg0W[0Wc0Y?0Y@0YA0YB0YC0YD0YE0YF0YG0YH0YI0YJ0YK0YL0YM0YN0YO0YP0YQ0YR0YS0YT0YU0YV0YW0YX0YY0YZ0Y[0ZQ0[G0\50]10]g0^]0_Y0`30`a0a70aQ0bM0cC0d;0e10eg0f70fE0fS0fa0fo0g=0gK0gY0gZ0g[0g\0g]0gl0gm0h?0hM0h[0iQ0il0jb0k00k>0kQ0l00lE0lZ0lo0m00m^0mm0nC0nQ0n_0nm0nn0no0o00o10o@0oA0oB0oP0ob10P11>11l12:12H12I12W12m13C13Y13Z13[13l14:14H14V14g14h14i15W16E17317417517617717817917:17;17<17=17J17W17X17Y17g18518C18n19Y1:D1:X1:i1;:S2PPS2FBS2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S2LF2PP3BUF2bs3LFB2FB3sp1FFS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB3PP03SLO3LOS2FB3sp13SP14SP1R2F0FFFFFS2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S1R3HIA2LF2PP2bs3LFB2FB3sp12h1S2LF2PP3BUF2bs3LFB2FB3sp1FFFFFFFFS2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S1R2LF2PP2lo2bs3LFB3LOS2FB3sp1S1R2LF2PP2lo2bs3LFB3LOS2FB3sp1S1R2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S1R3HIA1h2LF2sp2PP2bs3LFB3PP03TOP2FB3sp12h13SP15Ehtop4SP1R2F0FS2LF2PP2bs3LFB2FB3sp1S2LF2PP2AK3END2lo2bs3LFB2FB3sp11q3x253APC2x23x263x273x324POSTS2LF2PP3END2lo2bs3LFB2FB3sp11q3x253APP2x23x263x273x324POSTS2LF2PP2AK2bs3LFB2D1S2LF2PP2AK2bs3LFB2D1S2LF2PP3END3BUF2lo2bs3LFB2FB3sp11q3x253APB2x23x263x273x324POSTS2LF2PP3BUF2bs3LFB3DPBS2LF2PP2AK3END2lo2bs3LFB2FB3sp11q3x253APC2x23x263x273x324POSTS2LF2PP2AK3END2lo2bs3LFB2FB3sp11q3x253APC2x23x263x273x324POSTS2LF2PP3END2lo2bs3LFB2FB3sp11q3x253APP2x23x263x273x324POSTS2LF2PP2AK2bs3LFB2D1S2LF2PP1P3END2bs3LFB2FB3sp11q4Hqr03H24SS2LF2PP2bs3LFB3PP02FB3sp14SP1R2F02F8S1R3NS14STKe5STKe02sp2PP1P3END3BUF2lo2bs3PP02B13SLO3LOS2FB3sp11q3SP14Hqr03ALO3ACP2F0S2rg3RRgS1R3NS14STKe5STKe02sp2PP2lo2bs4PPLO3SLO3sp13SP1FS2LF2PP2bs3LFB2FB3sp12F02F8S1R3NS14STKe5STKe02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8S1P3END1q4Hqr02q24Hqr2FFS3sp1FS2PP1P3END2bs2FB3sp11q4Hqr0S2LF2PP1P3END2bs3LFB2FB3sp11q4Hqr0S2LF2PP1P3END2bs3LFB2FB3sp11q4Hqr0S3sp1S2PPFFS2rg3RRg2NES2LF2PP2bs3LFB2FB3sp1S1R3NS14STKe5STKe02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0FFFS2LF2bs3LFB2FBFS1R3NS14STKe5STKe02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS14STKe5STKe02sp2PP3BUF2lo2bs4PPLO3SLO3sp13SP15BUFLOS1R3HIA1h2sp2lo3TOP4HTOPS3BUF2bs2FB3APBS2loS1P3END3BUF2B12B51q4Hqr0S2PP3BUF2bs3DPBS2FBFS2LF2PP2bs3LFB2FB3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S2PP2bs2FB3APPS2LF2PP3END2bs3LFB2FB3sp12q22Lw3H25S1R2LF3slo2bs3LFB4SLOS2FB3sp13ALO2F1S2LF2PP2bs3LFB2FB3sp11c2HcFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOFSFFFS2LF2PP1P3END2bs3LFB2FB3sp11q4Hqr0S2LF2PP1P3END2bs3LFB2FB3sp11q4Hqr0S1P3END1q4Hqr02q24Hqr2FFFS1R3NS14STKe5STKe02sp2lo2bs3SLO2FB3sp13SP14FBLOFS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS14STKe5STKe02LF2sp2PP1P3END3BUF2lo2bs3LFB3PP02B12B32B53SLO3SPH2FB3sp11q4Hqr04SP1R2F05BUFLOS2PP2bs2FB3sp12F0S3BUF2bs3B47S1i2HiS2rg3RRg2E0FFFS1GFS1P3END3BUF2B12B51q4Hqr0FS1R2lo3LOSFFFFFFFFFFFFSFS2LF2bs3LFB2FBSS2sp2lo3sp13SP1S1R3NS14STKe5STKe02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2sp3sp1S1R3NS14STKe5STKe02LF2sp2PP1P3END3BUF2lo2bs3LFB3PP02B12B22B32B53SLO3SPH2FB3sp14SP1R2F05BUFLOFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14FBLOS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S1R3NS14STKe5STKe02LF2sp2AK2lo2bs3LFB4AKLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2AK2lo2bs3LFB4AKLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S2LF2PP2lo2bs3LFB4PPLO3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB4FBLOS2LF2sp2bs3LFB3sp13SP1S2LF2lo2bs3LFB2FB3sp14FBLOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15BUFLOS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2AK2lo2bs3LFB4AKLO3SLO3sp13SP1S1R2LF2sp2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2bs3LFB2FBFFFFS2LF3BUF2bs3LFBFS2LF2lo2bs3LFB3sp1S2LF2PP2bs3LFBS2LF2AK2bs3LFBS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S2LF2PP2bs3LFB2FB3sp12F02F8S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOPS2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3sp1FS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2bs3LFB3sp1S2LF2sp2bs3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBFFFFS2LF3BUF2bs3LFBFFS2LF2AK2bs3LFBS2LF2lo2bs3LFB3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2lo2bs3LFBS2LF2lo2bs3LFBFS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSFFS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOFFFFFFFFFFS1R2LF2bs3LFBS1R2LF2bs3LFBFFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB2FB2F0S2LF2bs3LFB2FB2F0". (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS D1 AKLO AK0 ALA DPB B5 B47 B3 B2 B1 BIN PPLO CWP PP0 ALP LFB STKe0 STKe GT NS1 IMG"]
  Lemma mid_walk2 : ltac2:(CDefT.buildp (gd_tbl_A_x509_akid_B ()) "PFB,$4.Psp1,$4.Ph1,(27.$11.VR,VHIA,)Pmm,P,(2.&40.)(3.(2.&8.))Pq,$4.Pk1,(2.&40.)Pk2,(2.&40.)Pk3,(2.&40.)Pk4,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Plenj,(2.&40.)P,(5.(12.(28.(;.&40.Vsp,)+90.)R1<.)(12.R1<.(28.(;.&40.Vsp,)+80.)))P,(6.$4.(29.R1=.+20.)=)P,(13.$11.VR,VHIA,R1=.VLB,(14.(15.$4.$4.)(16.$4.$4.R1?.+40.)VLF,)R1<.)P,(6.P,$4.Sp(22.$11.VR,VHIA,R1>.)(22.$11.VR,VHIA,Vh,))P,(6.$4.(2:.$11.VR,VHIA,R1?.)(2:.$11.VR,VHIA,Vh,))P,(6.$4.(2;.$11.VR,VHIA,R20.)(2;.$11.VR,VHIA,Vh,))P,(6.$4.(29.R23.+40.)=)P,(2<.VR,VLB,VLF,R24.+40.)P,(5.(12.VP,R21.)(12.R21.VEND,))P,(18.$11.R23.R26.(14.$19.(1:.R=.)(14.$19.(1:.R<.)(14.$19.(1:.R;.)(1;.$19.)))))P,(18.$11.R24.(:.R27.+20.)(14.$19.(1:.R;.)(1;.$19.)))P,(18.$11.R25.(:.(<.R28.+3.)(=.(>.VR,)))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.=))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(1;.$19.))))))))))P,(18.$11.R26.(:.(;.&40.Vsp,)-60.)(14.$19.(1:.Vs10,)(14.$19.(1:.Vs9,)(14.$19.(1:.Vs8,)(14.$19.(1:.Vs7,)(14.$19.(1:.Vs6,)(14.$19.(1:.Vs5,)(14.$19.(1:.Vs4,)(14.$19.(1:.Vs3,)(14.$19.(1:.Vs2,)(14.$19.(1:.Vs1,)(14.$19.(1:.Vs0,)(14.$19.(1:.Vra,)(1;.$19.))))))))))))))P,(18.$11.R27.(:.R29.+18.)(14.$19.(1:.(9.&40.R2:.))(1;.$19.)))P,(1=.$11.R28.(:.R2:.+20.)(:.(;.&40.Vsp,)-60.))P,(1=.$11.R29.R2;.(:.R2;.+18.))P,(1=.$11.R2:.Vlo,R2<.)P,(17.$11.R2;.)P,(18.$11.R2<.VPP,(14.$19.(1:.(9.&40.R2;.))(1;.$19.)))P,(18.$11.R2=.VAK,(14.$19.(1>.R2;.)(14.$19.(1>.R2:.)(14.$19.(1:.R29.)(14.$19.(1:.R28.)(1;.$19.))))))P,(18.$11.R2>.(:.VAK,+18.)(1?.Vct,Vcpad,===))P,(18.$11.R2?.(:.VAK,+38.)(14.$19.(1>.Vr1,)(14.$19.(1>.Vr2,)(14.$19.(1:.Vr3,)(14.$19.(1:.Vr4,)(1;.$19.))))))P,(20.$11.R30.VBUF,Vbs,)P,(21.$11.(>.VR,)(22.$11.VR,VHIA,Vh,)R31.VPP,+8.)P,(21.$11.(>.VR,)(22.$11.VR,VHIA,Vh,)R32.VAK,+50.)P,(21.$11.(>.VR,)(22.$11.VR,VHIA,Vh,)R33.VBUF,(23.(24.(2.&8.)Vbs,)))P,(2=.(12.(:.R37.+40.)VPP,)(12.(:.VPP,+8.)R37.))P,(2=.(12.(:.R38.+40.)VAK,)(12.(:.VAK,+50.)R38.))P,(25.$11.VR,VHIA,Vh,VLB,VLF,(;.&40.Vsp,)(;.&40.Vsp,)(14.(15.$4.$4.)(16.$4.$4.VPP,(:.VPP,+8.))(14.(15.$4.$4.)(16.$4.$4.VAK,(:.VAK,+50.))(1;.(15.$4.$4.))))Vm,R36.)P,(26.$11.(>.VR,)R37.Vslo,R39.)P,(26.$11.(>.VR,)R38.R3:.(;.&40.Vsp,))(2>.$11.(>.VR,)(22.$11.VR,VHIA,Vh,)(2?.R3<.R3;.R3:.)(7.(8.R33.(9.&40.R3;.)Vgp,Vtp,R32.R31.R30.Vsp,(9.&40.R3;.)R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(9.&40.R3<.)(9.&40.VPP,)(9.&40.VEND,)(9.&40.VAK,)(9.&40.(:.R3<.+20.))(9.&40.R3<.)(9.&40.(:.(<.R3<.+3.)(=.(>.VR,))))(9.&40.(=.(>.VR,)))(9.&40.(:.(<.VPP,+3.)(=.(>.VR,))))Vs11,R27.R26.R25.R24.)VF,(9.&40.+:;82<.)Vfc,(?.(2.&40.))R39.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros until lenj.
  intros SP1 SP1M HH1 Ehcs Ehtop Estk F64 FRSH Hqr0 FHD HLEN FSH SAVE SLOT SThi STmid STlo MI HPP HA0 HHD HA56 HBUF OPP OAK OBUF APP APC PRES SS1 SS2.
  rt_facts.
  unfold seq_cells in HHD.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP.
  rewrite Ehtop, Estk in HTOP.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKe0; lia | lx_side_lia ]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKe0 TOP HTOP; lia | lx_side_lia ]]).
  assert (SCS1 : crange CS lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]).
  destruct (frame_factsA R HIA CS h1 LB LF mm FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
  assert (BINA : In (BUF, n) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; left; exact BIN).
  assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h1 LB _ mm LB HH1 ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
  assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) PP 8)
    by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]).
  assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
  assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_abase asegs R HIA h1 _ _ mm HH1) as AB0.
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  lx_pre. lx_run_tac (PLAN [0x052ef8; 0x09990c; 0x0ab6e4; 0x0ab88c; 0x0ae500] [(0xab7fc, DJoin); (0xab8fc, DJoin); (0xab940, DSplit)] 266%N).
  lx_tree.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xab850) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9990c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try clear Kq; try clear AB0| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename mg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH (FB + 32) 1%nat as OLEN | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with HHx : HM _ _ _ h1 _ _ mg |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mg HHx) as ABg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => pose proof GT as SPT | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "GT3-CALL" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply SPT with (CS := CS) (PP := PP) (LENP := FB + 32) (P := q) (END := END) (BUF := BUF) (bs := bs) (tag := 161) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | lazymatch goal with | |- BUF + _ < 2 ^ 63 => first [ clear - B47; lia | lx_side_lia ] | |- _ \/ _ => first [ clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 STKe0 F1 FBLO ALO LOS; lia | lx_side_lia ] | |- _ => clear - SP1 SP1M SLO NS1 STKe0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3 Hqr0; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "GT3-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try clear SPT; try clear OLEN| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Lw into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename q2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename rg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HLg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?lx_rv = 0 -> _ |- _ => rename H into HLg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename RRg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ < rg <= 0 |- _ => rename H into RRg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hqr2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : q <= q2 <= _ |- _ => rename H into Hqr2 end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xaaefc: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052ef8; 0x09990c; 0x0ab6e4; 0x0ab88c; 0x0ae500] [(0xab7fc, DJoin); (0xab8fc, DJoin); (0xab940, DSplit)] 266%N); lx_tree | |- _ => idtac end.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  all: (cut True; [ intros _ | ]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: match goal with E_ : ?lxq = ?lxq |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ ?lxq (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "NOISSUER") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (destruct (x509_mismatch_select q END 18446744073709542042 ltac:(first [ clear - Hqr0 B1 B5; lia | lx_side_lia ]) ltac:(first [ clear - Hqr0 B1 B5; lia | lx_side_lia ]) ltac:(clear; lia)) as (r' & ER & R1 & R2)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (change 18446744073709551615 with (Z.ones 64)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (rewrite Z.land_ones by (clear; lia)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (change (2 ^ 64) with 18446744073709551616) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (rewrite ER) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear ER| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (fin_exq r' q) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [destruct (Z.eq_dec q END) as [E|NE]; [apply R1 in E; first [ clear - E; lia | lx_side_lia ]| specialize (R2 NE); first [ clear - R2; lia | lx_side_lia ]]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [exact Hqr0|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (spine; first [ eassumption | (intros E0; destruct (Z.eq_dec q END) as [EE|NE]; [exact EE| exfalso; specialize (R2 NE); first [ clear - R2 E0; lia | lx_side_lia ]]) | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "NOISS-EXQ-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xaadb8 path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xaadb8 path 1: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: match goal with E_ : ?lxq = ?lxq |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ ?lxq (seg_rom _)] => idtac | |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "GT3-ERR") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (errsum RRg) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (fin_exq_e q2) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - RRg; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - Hqr0 Hqr2; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (spine; first [ eassumption | (intros E0; exfalso; first [ clear - E0 RRg; lia | lx_side_lia ]) | (intros E0; exfalso; first [ clear - E0; lia | lx_side_lia ]) | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "ERR3-EXQ-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xaadb8 path 2: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xaadb8 path 2: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xab88c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (subst rg) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (destruct (HLg eq_refl) as [Hq2 HqL2]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HLg; try clear Kz; try clear RRg| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mx HHx) as AB3 end end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear AB3| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "CALLQ") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (fold_head) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (right) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold CALLQ) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (exists q2) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat (lazymatch goal with |- ex _ => eexists end)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - Hqr0 Hqr2; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - HqL2; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (spine; first [ eassumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "CALLQ-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xaaf20 path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xab88c) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xaaf20 path 1: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xab88c) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- True => exact I | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lxw mid_walk2: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EXQ3 (FB sp1 : Z) (h3 : HST asegs R HIA) (LBc : list blk) (m4 : mem) (hct hcpad : word) (hcl hcp hcn : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_akid_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm5,P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Lw0,(2.&40.)(1.(2.&40.)Lw1,(2.&40.)(1.(2.&40.)Lw2,(2.&40.)(1.(2.&40.)Lk1,(2.&40.)(1.(2.&40.)Lk2,(2.&40.)(1.(2.&40.)Lk3,(2.&40.)(1.(2.&40.)Lk4,(2.&40.)(1.(2.&40.)Lq1,(2.&40.)(1.(2.&40.)Lq2,(2.&40.)(1.(2.&40.)Lq3,(2.&40.)(1.(2.&40.)Lq4,(2.&40.)(1.(2.&40.)Lxra,(2.&40.)(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)Lx11,(2.&40.)(1.(2.&40.)Lx12,(2.&40.)(1.(2.&40.)Lx13,(2.&40.)(1.(2.&40.)Lx14,(2.&40.)(1.(2.&40.)Lx15,(2.&40.)(1.(2.&40.)Lx16,(2.&40.)(1.(2.&40.)Lx17,(2.&40.)(1.(2.&40.)Ls3v,(2.&40.)(1.(2.&40.)Ls4v,(2.&40.)(1.(2.&40.)Ls5v,(2.&40.)(1.(2.&40.)Ls6v,(2.&40.)(1.(2.&40.)Ls9v,(2.&40.)(1.(2.&40.)Ls10v,(2.&40.)(1.(2.&40.)Lx28,(2.&40.)(1.(2.&40.)Lx29,(2.&40.)(1.(2.&40.)Lx30,(2.&40.)(1.(2.&40.)Lx31,(2.&40.)(5.(6.$0.R24.(7.(8.R15.(9.&40.O9.)Vgp,Vtp,R14.R13.R12.Vsp,(9.&40.O9.)(9.&40.R22.)R11.R10.R?.R>.R=.R<.R;.(9.&40.O:.)R:.R9.R8.R7.(9.&40.O:.)(9.&40.(:.(<.O:.+3.)(=.(>.VR,))))R6.R5.Vs11,R4.R3.R2.R1.)VF,(9.&40.+:;6>4.)Vfc,(?.(2.&40.))R23.(10.$11.)))(5.(5.(30.-3000.R22.)(12.R22.=))(5.(5.(12.VP,R21.)(12.R21.VEND,))(5.(13.$11.VR,VHIA,O8.(31.$32.O7.VLB,)(14.(15.$4.$4.)(16.$4.$4.O:.+40.)VLF,)R23.)(5.(17.$11.R23.)(5.(18.$11.R23.O:.(14.$19.(1:.R20.)(14.$19.(1:.R1?.)(14.$19.(1:.R1>.)(1;.$19.)))))(5.(18.$11.R23.(:.(<.O:.+3.)(=.(>.VR,)))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.=))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(1;.$19.))))))))))(5.(18.$11.R23.(:.(;.&40.Vsp,)-60.)(14.$19.(1:.Vs10,)(14.$19.(1:.Vs9,)(14.$19.(1:.Vs8,)(14.$19.(1:.Vs7,)(14.$19.(1:.Vs6,)(14.$19.(1:.Vs5,)(14.$19.(1:.Vs4,)(14.$19.(1:.Vs3,)(14.$19.(1:.Vs2,)(14.$19.(1:.Vs1,)(14.$19.(1:.Vs0,)(14.$19.(1:.Vra,)(1;.$19.))))))))))))))(5.(18.$11.R23.(:.O9.+18.)(14.$19.(1:.(9.&40.O:.))(1;.$19.)))(5.(1=.$11.R23.(:.O9.+20.)(:.(;.&40.Vsp,)-60.))(5.(1=.$11.R23.O9.(:.O9.+18.))(5.(1=.$11.R23.Vlo,O9.)(5.(18.$11.R23.VPP,(14.$19.(1:.(9.&40.R21.))(1;.$19.)))(5.(18.$11.R23.VAK,(14.$19.(1>.R1=.)(14.$19.(1>.R1<.)(14.$19.(1:.R1;.)(14.$19.(1:.R1:.)(1;.$19.))))))(5.(18.$11.R23.(:.VAK,+18.)(1?.O5.O4.O3.O2.O1.))(5.(18.$11.R23.(:.VAK,+38.)(14.$19.(1>.R19.)(14.$19.(1>.R18.)(14.$19.(1:.R17.)(14.$19.(1:.R16.)(1;.$19.))))))(5.(25.$11.VR,VHIA,O8.VLB,VLF,(;.&40.Vsp,)(;.&40.Vsp,)(14.(15.$4.$4.)(16.$4.$4.VPP,(:.VPP,+8.))(14.(15.$4.$4.)(16.$4.$4.VAK,(:.VAK,+50.))(1;.(15.$4.$4.))))Vm,R23.)(5.(25.$11.VR,VHIA,O8.(31.$32.O7.VLB,)VLF,(;.&40.Vsp,)(;.&40.Vsp,)(14.(15.$4.$4.)(16.$4.$4.VPP,(:.VPP,+8.))(14.(15.$4.$4.)(16.$4.$4.VAK,(:.VAK,+50.))(1;.(15.$4.$4.))))O6.R23.)(5.(26.$11.(>.VR,)R23.Vslo,O9.)(5.(26.$11.(>.VR,)R23.O9.(;.&40.Vsp,))P,(6.$4.R22.=)(6.$4.R22.VEND,))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 CWA56; try lx_pin1 CWHD; try lx_pin1 CWA0; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 B2; try lx_pin1 r4; try lx_pin1 r3; try lx_pin1 r2; try lx_pin1 r1; try lx_pin1 cpad; try lx_pin1 ct; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04[0@C40858145355.232C60410007123.231D10636937134.232D10637083018.180D14196765254.180D14197109858.232D16071854214.232D17155136187.181D2457516971.232 D2459793318.179 D31397812764.181D3162115617.232 D3162359813.180 D32452690557.179D32458870384.232D3374278032.178 D33985273631.181D36106837480.180D36107017164.232D40273911871.181D43016287775.182D45715803169.178D46794843979.232D46795284847.180D53294739978.181D60109265000.181D60109265003.180D60109446735.232D61460510894.232D62011770190.182D64997949699.179D65008160014.232D68405837779.178D6909504982.178 K18493193506.232K20981739667.230K24799944541.232K27175203321.232K29378133114.232K30993319891.232K34158808196.232K59453006468.232K65858155712.231K68239931741.232L11386738373.196L11386738502.195L17605293693.153L17607390833.160L17705907808.2  L18489062900.25 L18497025716.2  L19546883928.153L19548981076.160L19698472309.33 L20977711877.2  L21654730866.2  L22420726575.170L24206288344.1  L24754814165.197L24754814294.196L24812802884.2  L2621559066.1   L27111942217.1  L27162377696.2  L27206487025.3  L27380263923.3  L27821999381.206L27938631862.33 L28344346468.2  L29391009772.3  L29900236891.33 L30319686129.33 L30997223346.3  L31168734358.148L31170831514.155L34023826209.0  L34171225874.2  L34327243841.1  L3484573471.33  L35236225328.25 L35655538631.11 L35903316071.25 L38235734261.1  L38865218625.1  L41110154015.25 L41251426164.1  L41359293650.2  L42612502460.195L43202358962.164L43305107741.25 L43809418676.195L4472687353.166 L45363093875.185L47870616696.2  L4809844382.2   L48117620900.148L48119718056.155L48119718057.156L48119718063.149L48132302223.187L48132302231.186L48257107102.2  L49233373885.2  L5021251703.1   L50678314462.3  L50790731766.11 L52840517793.6  L53359885363.2  L55195235631.25 L55432526301.2  L56380991837.10 L57387013260.33 L58972524609.3  L59249556020.1  L59308586248.2  L59308660947.3  L59314873579.2  L59314873579.3  L59314873579.4  L59314988138.1  L59314988138.198L59314988138.2  L59448584466.2  L60098763854.6  L62275882349.3  L63344940145.2  L64179129035.1  L64482796004.3  L65862516566.2  L66812728480.3  L67070089790.2  L67556946858.2  L67922604617.0  L68244403524.2  L6910010093.155 L6912107233.148 L8176033733.195 L8176033733.196 L881835912.0    L9080220944.4   L9356559676.16  L9783143000.2   L9817154577.195 L9817154577.196 O11096106305.232O11640932009.231O14614127145.229O14912726833.229O19003878908.232O20866770946.232O21230138846.231O22525005962.231O2384783454.229 O31189574615.232O32135033303.232O3493317847.230 O37559489567.232O3821773283.232 O41068820901.232O424351700.230  O44938202843.230O45626564938.231O48557518091.232O48841645583.231O49539471840.232O49701823576.229O50011839873.230O55209884805.230O55240955659.232O56187274208.232O62594918972.231P21647862485.230P27200772438.229P28346987971.231P41371876950.231P47876372191.230P4804097081.232 P48262927929.232P49230739482.229P50671478649.230P53363783589.231P55446727546.231P62260666314.230P63339218646.231P64484389699.229P66818508295.232P67064334489.229P67551224077.232Q10521014457.196Q10523111605.189Q10588139941.206Q10592386206.186Q10592533181.232Q10594483354.193Q10636937134.232Q10637083020.187Q10637083914.199Q10639180168.194Q11133374175.232Q11657053839.232Q11657494700.186Q11659591848.193Q12658527498.201Q14851060497.203Q14851060498.204Q16071854214.232Q17027695041.232Q17155136177.188Q17157233329.200Q17157233341.195Q17681074618.232Q17752725157.232Q17771329073.189Q17773426237.196Q19551029871.206Q21767670690.232Q23216651711.193Q23218748859.186Q23219026840.232Q23925414032.196Q23925414038.205Q23927511196.189Q27573751300.232Q2803826605.232 Q29775981542.232Q31158247845.185Q31158247869.192Q31168734358.190Q31170831510.202Q31170831514.197Q32440833928.185Q32440833936.192Q32679790546.193Q32679790549.196Q32681607669.232Q32681887702.186Q32681887705.189Q33194651983.201Q33983176469.200Q33983176473.195Q33985273621.188Q35594771431.194Q35596721601.232Q35596868579.187Q35655619522.203Q38250992820.203Q38250992823.204Q40216052035.185Q40216052059.192Q40259924710.206Q42437284302.235Q42439168719.232Q42441479404.209Q46793187693.194Q46794843979.232Q46795284841.187Q46795285999.199Q47228624636.196Q47230721776.189Q48117620904.186Q48118064779.232Q48119718060.193Q48132302223.192Q48132302231.185Q49561274036.196Q49563371192.189Q49746198710.232Q49746346514.234Q49748444822.207Q53576838845.232Q56525516072.192Q56525516080.185Q56530976407.232Q56531220660.186Q56533317808.193Q57828105177.232Q60111362155.203Q62009673032.196Q62009673038.205Q62011770180.189Q63909620151.193Q63911276432.232Q63911717299.186Q67038703949.232Q67039048681.234Q67041146733.207Q6897428426.192 Q6897428434.185 Q6910010081.202 Q6910010093.197 Q6912107233.190 Q8697078920.235 Q8699324297.232 Q8701272490.209 Q8877967471.192 Q8877967479.185 Q9356559674.209 Q9640321936.206 Q9644583048.232 00000400800P00h00i00j02502M02N02O02P02Q02R02j03B03C03[03\03]03^04?04W04o05G05H05i06J06k07m08G08_09709809P0:N0;I0;]0<10=00=F0>D0?B0@=0@Q0AS0AT0B?0Bj0C20Ca0Cb0D@0D^0Ef0Eg0Eh0FK0FP0GF0GG0GH0GM0GQ0GR0GS0G^0H60I@0IA0IB0JV0K10K20K@0KN0KO0KP0KT0LY0MR0Mk0N:0N>0NB0NQ0NU0NV0Nn0Od0P20PX0Q<0QY0QZ0Q[0RI0S70Se0TS0UA0Uo0V00V10V20V30VS0Vi0Vj0WY0WZ0X30XD0XP0XT0XZ0Xe0Xf0Xg0Xh0Xk0Xl0Xm0Xn0Y80Y90Y:0Y;0Y<0Y=0Y>0Y?0Y@0YA0YB0YP0Y^0[V0]N0]O0]^0^R0^Z0`M0b@0bA0bB0bC0bD0bE0bF0bG0bH0bI0bJ0bK0bL0bM0bN0bO0bP0bQ0bR0bS0bT0bU0bV0bW0bX0bY0bZ0b[0b\0cX0dN0e<0f20fh0g^0hT0hn0ib0j80jR0kH0l>0m60ml0nb0o20oB0oP0o^0ol10:10H10V10d11211@11A11B11C11R11S11e12W12e13313A13O14E15;15<15=15[16Q16_16m17;17[17n18N18O18^19419B19P19^19l1::1:;1:<1:=1:>1:?1:@1:A1:P1:^1:l1;:1;;1;<1;=1;`1;n1<<1<=1<>1<L1<b1=81=N1=\1=j1>81>F1>W1>h1?V1@D1A21A`1BN1BO1BP1C41CX1D<1D=1D>1D?1D@1DA1DB1Dj1E>1EK1EX1Ee1Ef1Eg1Eh1FZ1GL1H>1HL1HZ1Hh1I61ID1J01J\1KH1KI1KJ1K^1Ko1L@S2PPS2FBS2LF2PP2AK2bs3LFB2FB3sp1S2LF2PP2AK2bs3LFB2FB3sp1FFS1R3NS14STKe5STKe02LF2sp2PP2AK2lo2bs3LFB3PP03AK03SLO3LOS2FB3sp13SP14SP1R2F0S2LF2PP2AK2bs3LFB2FB3sp1FFFFFS2LF2PP2AK2bs3LFB2FB3sp1S2LF2PP2AK2bs3LFB2FB3sp1FS2LF2PP2AK2bs3LFB2FB3sp1FFFS1R3HIA2LF2PP2AK2bs3LFB2h32FB3sp1S2LF2PP2AK2bs3LFB2FB3sp1S2LF2PP2AK2bs3LFB2FB3sp1S2LF2PP2AK2bs3LFB2FB3sp1FS1R2LF2PP2AK2lo2bs3LFB3LOS2FB3sp1S1R2LF2PP2AK2lo2bs3LFB3LOS2FB3sp1S1R2LF2PP2AK2lo2bs3LFB3LOS2FB3sp1S1R3HIA1h2LF2sp2PP2AK2bs3LFB3PP03AK03TOP2h32FB3sp13ET33SP14SP1R2F0S1R2LF2PP2AK2bs3LFB2FB3sp1S2LF2PP2AK2bs3LFB2FB3sp1S2LF2PP2AK2bs3LFB2FB3sp1FS2LF2PP2AK2bs3LFB2FB3sp1S2LF2PP2AK3END2lo2bs3LFB2FB3sp12p43x243APC2x23x253x263x274POSTS2LF2PP3END2lo2bs3LFB2FB3sp12p43x243APP2x23x253x263x274POSTS2LF2PP2AK2bs3LFB2D1S2LF2PP2AK2bs3LFB2D1S2LF2PP3END3BUF2lo2bs3LFB2FB3sp12p43x243APB2x23x253x263x274POSTS2LF2PP3BUF2bs3LFB3DPBS2LF2PP2AK3END2lo2bs3LFB2FB3sp12p43x243APC2x23x253x263x274POSTS2LF2PP2AK3END2lo2bs3LFB2FB3sp12p43x243APC2x23x253x263x274POSTS2LF2PP3END2lo2bs3LFB2FB3sp12p43x243APP2x23x253x263x274POSTS2LF2PP2AK2bs3LFB2D1S2LF2PP2AK1P3END2bs3LFB3PP03AK02FB3sp12p43Hp44SP1R2F02q22Lw3H292H1FS2LF2PP2AK2bs3LFB3PP03AK02FB3sp14SP1R2F82F0S2LF2PP2AK2bs3LFB3PP03AK02FB3sp14SP1R2F82F0S2rg3RRgS1R3NS14STKe5STKe02sp2PP2lo2bs4PPLO3SLO3sp13SP1FS2LF2PP2AK2bs3LFB2FB3sp12F82F0S2LF2PP2AK2bs3LFB2FB3sp12F82F0S1R3NS14STKe5STKe02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F82F0FFS2LF2PP2AK2bs3LFB2FB3sp12rc3RR33H25S3sp1S2LF2PP2AK3END2bs3LFB3PP03AK02FB3sp14SP1R2F02q22Lw3H26FFS3sp1S2PPFFS2rg3RRg2NES2LF2PP2AK2bs3LFB2FB3sp1S1R3NS14STKe5STKe02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0FFS1R3NS14STKe5STKe02sp2PP1P3END3BUF2lo2bs3PP02B13SLO3LOS2FB3sp12p43SP13Hp43ALO3ACP2F0S2PP1P3END2bs2FB3sp12p43Hp4FS2LF2bs3LFB2FBS2LF2bs3LFB2FBSFS2AKS1R3NS14STKe5STKe02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS14STKe5STKe02sp2PP3BUF2lo2bs4PPLO3SLO3sp13SP15BUFLOS1R3HIA1h2sp2lo3TOP5HTOP3S3BUF2bs2FB3APBS2loS2AKS2PP3BUF2bs3DPBS2FBFS2LF2PP2AK2bs3LFB2FB3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14FBLOS2PP2bs2FB3APPS2LF2PP2AK3END2bs3LFB2FB3sp12q22Lw3H28S1R2LF3slo2bs3LFB4SLOS2FB3sp13ALO2F1S2LF2PP2AK2bs3LFB2FB3sp11c2HcFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOFFFFS1R3NS14STKe5STKe02sp2lo3SLO3LOSS1P3END2p43Hp42q24Hqr2FS1R3NS14STKe5STKe02sp2lo2bs3SLO2FB3sp13SP14FBLOFS1R3BUF2lo2bs3LOS3ALO3BCES2PP2bs2FB3sp12F0S3BUF2bs3B47S2AKS1i2HiS2rg3RRg2E0FFFS1GFFFS1R2lo3LOSFFFFFFFFSFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3NS14STKe5STKe02LF2sp2PP2AK1P3END3BUF2lo2bs3LFB3PP02B12B32B53AK03SLO3SPH2FB3sp12p43Hp44SP1R2F05BUFLO2q22Lw3H283H292H1S1R3NS14STKe5STKe02LF2sp2PP2AK1P3END3BUF2lo2bs3LFB3PP02B12B32B53AK03SLO3SPH2FB3sp12p43Hp44SP1R2F05BUFLO2q22Lw3H283H292H1SS2sp2lo3sp13SP1S1R3NS14STKe5STKe02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2sp3sp1S1R3NS14STKe5STKe02LF2sp2PP2AK1P3END3BUF2lo2bs3LFB3PP02B12B32B53AK03SLO3SPH2FB3sp12p43Hp44SP1R2F05BUFLO2q24Hqr23H29S1R3NS14STKe5STKe02LF2sp2PP2AK1P3END3BUF2lo2bs3LFB3PP02B12B32B53AK03SLO3SPH2FB3sp12p43Hp44SP1R2F05BUFLO2q24Hqr23H29FFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14FBLOS1R3NS14STKe5STKe02LF2sp2AK2lo2bs3LFB4AKLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2AK2lo2bs3LFB4AKLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14FBLOS2LF2PP2lo2bs3LFB4PPLO3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3ALO2F1S2LF2sp2bs3LFB3sp13SP1S2LF2lo2bs3LFB2FB3sp14FBLOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14FBLOS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15BUFLOS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2AK2lo2bs3LFB4AKLO3SLO3sp13SP1S1R2LF2sp2bs3LFBS1R2LF2sp2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2bs3LFB2FBFFFS2LF3BUF2bs3LFBFS2LF2lo2bs3LFB3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP1S2LF2PP2bs3LFBS2LF2AK2bs3LFBS2LF2AK2bs3LFBS2LF2AK2bs3LFBS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2AK2lo2bs3LFB4AKLO3SLO3sp13SP1FFS2LF2PP2AK2bs3LFB2FB3sp12F82F0S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3LFB3TOP5HTOP3S1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP5HTOP3FS2LF2bs3LFB3sp1S2LF2sp2bs3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBFFFFFFFS2LF3BUF2bs3LFBS2LF2AK2bs3LFBS2LF2AK2bs3LFBS2LF2AK2bs3LFBFFFS1R3HIA1h2LF2sp2lo2bs3LFB3TOP5HTOP3S2LF2lo2bs3LFBS2LF2lo2bs3LFBFFS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2bs3LFB3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15HTOP3S1R3HIA1h2LF2sp2bs3LFB3TOP3sp15HTOP3S1R3HIA1h2LF2sp2bs3LFB3TOP3sp15HTOP3FFFFFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15HTOP3S1R2LF2lo2bs3LFB3LOSS1R2LF2bs3LFBS1R2LF2bs3LFBS1R2LF2bs3LFBFFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15HTOP3S1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15HTOP3S1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15HTOP3FFS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB2FB2F0S2LF2bs3LFB2FB2F0". (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS D1 DAB AKLO CWA AK0 ALA DPB B5 B47 B3 B1 BIN PPLO CWP PP0 ALP LFB STKe0 STKe GT NS1 IMG"]
  Lemma post_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_akid_B ()) "Ph3,(27.$11.VR,VHIA,)PLBc,(33.$32.)PFB,$4.Psp1,$4.Pm4,P,(2.&40.)(3.(2.&8.))Prc,$4.Pp4,$4.Phct,(2.&40.)Phcpad,(2.&40.)Phcl,$4.Phcp,$4.Phcn,$4.Pk1,(2.&40.)Pk2,(2.&40.)Pk3,(2.&40.)Pk4,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Plenj,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(13.$11.VR,VHIA,R22.(31.$32.R21.VLB,)(14.(15.$4.$4.)(16.$4.$4.R20.+40.)VLF,)R1>.)P,Px,$4.P,(22.$11.VR,VHIA,Vh,R1.)(22.$11.VR,VHIA,R25.R2.)P,(6.$4.(2:.$11.VR,VHIA,R24.)(2:.$11.VR,VHIA,Vh,))P,(6.$4.(2;.$11.VR,VHIA,R25.)(2;.$11.VR,VHIA,Vh,))P,(5.(12.(28.(;.&40.Vsp,)+90.)R23.)(12.R23.(28.(;.&40.Vsp,)+80.)))P,(6.$4.(29.R24.+20.)=)P,(6.$4.(29.R26.+40.)=)P,(2<.VR,VLB,VLF,R27.+40.)P,(2<.VR,(31.$32.R29.VLB,)VLF,R28.+40.)P,(34.(22.$11.VR,VHIA,Vh,)R29.+40.)P,(5.(30.-3000.R27.)(12.R27.=))P,(5.(12.VP,R27.)(12.R27.VEND,))P,(18.$11.R2:.R2<.(14.$19.(1:.R1>.)(14.$19.(1:.R1=.)(14.$19.(1:.R1<.)(1;.$19.)))))P,(18.$11.R2;.(:.R2=.+20.)(14.$19.(1:.R1<.)(1;.$19.)))P,(18.$11.R2<.(:.(<.R2>.+3.)(=.(>.VR,)))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.+?1.))(14.$19.(1<.(9.&8.=))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(14.$19.(1<.(9.&8.+?3.))(1;.$19.))))))))))P,(18.$11.R2=.(:.(;.&40.Vsp,)-60.)(14.$19.(1:.Vs10,)(14.$19.(1:.Vs9,)(14.$19.(1:.Vs8,)(14.$19.(1:.Vs7,)(14.$19.(1:.Vs6,)(14.$19.(1:.Vs5,)(14.$19.(1:.Vs4,)(14.$19.(1:.Vs3,)(14.$19.(1:.Vs2,)(14.$19.(1:.Vs1,)(14.$19.(1:.Vs0,)(14.$19.(1:.Vra,)(1;.$19.))))))))))))))P,(18.$11.R2>.(:.R2?.+18.)(14.$19.(1:.(9.&40.R30.))(1;.$19.)))P,(1=.$11.R2?.(:.R30.+20.)(:.(;.&40.Vsp,)-60.))P,(1=.$11.R30.R31.(:.R31.+18.))P,(1=.$11.R31.Vlo,R32.)P,(17.$11.R32.)P,(18.$11.R33.VPP,(14.$19.(1:.(9.&40.R31.))(1;.$19.)))P,(18.$11.R34.VAK,(14.$19.(1>.R2<.)(14.$19.(1>.R2;.)(14.$19.(1:.R2:.)(14.$19.(1:.R29.)(1;.$19.))))))P,(18.$11.R35.(:.VAK,+18.)(1?.R32.R31.R30.R2?.R2>.))P,(18.$11.R36.(:.VAK,+38.)(14.$19.(1>.Vr1,)(14.$19.(1>.Vr2,)(14.$19.(1:.Vr3,)(14.$19.(1:.Vr4,)(1;.$19.))))))P,(20.$11.R37.VBUF,Vbs,)P,(21.$11.(>.VR,)(22.$11.VR,VHIA,R3<.)R38.VPP,+8.)P,(21.$11.(>.VR,)(22.$11.VR,VHIA,R3=.)R39.VAK,+50.)P,(21.$11.(>.VR,)(22.$11.VR,VHIA,R3>.)R3:.VBUF,(23.(24.(2.&8.)Vbs,)))P,(2=.(12.(:.R3=.+40.)VPP,)(12.(:.VPP,+8.)R3=.))P,(2=.(12.(:.R3>.+40.)VAK,)(12.(:.VAK,+50.)R3>.))P,(25.$11.VR,VHIA,R41.VLB,VLF,(;.&40.Vsp,)(;.&40.Vsp,)(14.(15.$4.$4.)(16.$4.$4.VPP,(:.VPP,+8.))(14.(15.$4.$4.)(16.$4.$4.VAK,(:.VAK,+50.))(1;.(15.$4.$4.))))Vm,R3=.)P,(26.$11.(>.VR,)R3>.Vslo,R3?.)P,(26.$11.(>.VR,)R3?.R40.(;.&40.Vsp,))(2>.$11.(>.VR,)(22.$11.VR,VHIA,R44.)(35.R42.R41.R44.R43.R40.R3=.R3<.R3;.R3:.R39.)(7.(8.(9.&40.+:;890.)(9.&40.R41.)Vgp,Vtp,R30.R2?.R2>.Vsp,(9.&40.R41.)(9.&40.R3?.)R2=.R2<.R2;.R2:.R29.R28.R27.(9.&40.R42.)(9.&40.VPP,)(9.&40.VEND,)(9.&40.VAK,)(9.&40.(:.R42.+20.))(9.&40.R42.)(9.&40.(:.(<.R42.+3.)(=.(>.VR,))))(9.&40.(=.(>.VR,)))(9.&40.(:.(<.VPP,+3.)(=.(>.VR,))))Vs11,R26.R25.R24.R23.)VF,(9.&40.+:;890.)Vfc,(?.(2.&40.))R40.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros until x31.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB RR3 Hp4 FHD HLEN FSH SAVE SLOT SThi STmid STlo MI HPP HA0 HHD HA56 HBUF OPP OAK OBUF APP APC PRES SS1 SS2.
  pose proof (hcs_stack asegs R HIA h) as SCS0.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (cs_ok_sb _ _ CSOK3) as SB64.
  pose proof (art_alwf asegs R HIA) as ALWF'.
  unfold al_wf in ALWF'.
  pose proof IMG as IMG'.
  unfold asan_img_ok in IMG'.
  pose proof (art_lo asegs R HIA) as ALO.
  pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
  pose proof (alloc_ceiling_val R) as ACV.
  unfold A_x509_akid_A.STKk in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold seq_cells in HHD.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKe0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 64) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKe0 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS13 : crange (hcs asegs R HIA h3) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS3| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  clear SCS SCS0.
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF m4 FB 64 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (_ & INF & INH3 & IND3 & AP3 & _ & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  pose proof FRSH as FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
  assert (BIN3 : In (BUF, n) (LBc ++ LB)) by (apply in_app_iff; right; exact BIN).
  assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h3 _ _ m4 (LBc ++ LB) HH3 ltac:(intros b Hb; exact Hb) _ BIN3) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
  assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
  assert (WCA : wcover R LB LF (bv_unsigned sp) W AK 80) by (apply wcover_inside; cbn [inside]; right; left; clear; lia).
  assert (WCP2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
  assert (WCA2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) W AK 80) by (apply wcover_inside; cbn [inside]; right; left; clear; lia).
  pose proof (presW_init_at R HIA h3 _ _ (LBc ++ LB) LF m4 (bv_unsigned sp) (bv_unsigned sp) W h3 HH3
    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(first [ clear - LOS SLO NS1 STKe0; lia | lx_side_lia ])) as PRES2.
  pose proof (art_stk_high asegs R HIA) as STKH.
  assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
  assert (WLc : wlow R (LBc ++ LB) LF) by (split; [exact (proj2 (proj2 (proj2 PRES2)))| apply (art_data_lo asegs R HIA)]).
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 64) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (CWP3 : client_wrange L ((LBc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUB1]).
  assert (CWA3 : client_wrange L ((LBc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) AK 80) by (eapply client_wrange_mono; [exact CWA| exact SUB1]).
  try (pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP). try (rewrite Ehtop, Estk in HTOP). try (assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKe0; lia)). try (assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKe0 TOP HTOP; lia])).   (* [comment removed for export] *)
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  lx_pre. lx_run_tac (PLAN [0x052ef8; 0x09990c; 0x0ab6e4; 0x0ab82c; 0x0ae500] [(0xab7fc, DJoin); (0xab8fc, DJoin); (0xab940, DSplit)] 266%N).
  lx_tree.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xab8a8) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9990c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try lx_r0 rc | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => subst rc | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear K3; try clear RR3| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename mg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH (FB + 32) 1%nat as OLEN | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with HHx : HM _ _ _ h3 _ _ mg |- _ => pose proof (hm_abase asegs R HIA h3 _ _ mg HHx) as ABg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => pose proof GT as SPT | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "GT4-CALL" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA h3) (PP := PP) (LENP := FB + 32) (P := p4) (END := END) (BUF := BUF) (bs := bs) (tag := 130) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | lazymatch goal with | |- BUF + _ < 2 ^ 63 => first [ clear - B47; lia | lx_side_lia ] | |- _ \/ _ => first [ clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 STKe0 F1 FBLO ALO LOS; lia | lx_side_lia ] | |- _ => clear - SP1 SP1M SLO NS1 STKe0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B3 Hp4; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "GT4-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try clear SPT; try clear OLEN| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => idtac "GT4-BACK" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Lw into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename q2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename rg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HLg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?lx_rv = 0 -> _ |- _ => rename H into HLg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename RRg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ < rg <= 0 |- _ => rename H into RRg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hqr2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : p4 <= q2 <= _ |- _ => rename H into Hqr2 end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xaaf38: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052ef8; 0x09990c; 0x0ab6e4; 0x0ab82c; 0x0ae500] [(0xab7fc, DJoin); (0xab8fc, DJoin); (0xab940, DSplit)] 266%N); lx_tree | |- _ => idtac end.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  all: (cut True; [ intros _ | ]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: match goal with E_ : ?lxq = ?lxq |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ ?lxq (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "CALLEE-ERR") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with H : rw_cells _ ?mxc (AK + 24) _ |- _ => change (rw_cells asegs mxc (AK + 24) (seq_cells hct hcpad hcl hcp hcn)) in H end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold EXQ3) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (exists rc, p4) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat (lazymatch goal with |- ex _ => eexists end)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [exact RR3|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [exact Hp4|]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xaadb8 path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xaadb8 path 1: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: match goal with E_ : ?lxq = ?lxq |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ ?lxq (seg_rom _)] => idtac | |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "GT4-ERR") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with H : rw_cells _ ?mxc (AK + 24) _ |- _ => change (rw_cells asegs mxc (AK + 24) (seq_cells hct hcpad hcl hcp hcn)) in H end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold EXQ3) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (eexists) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (exists q2) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat (lazymatch goal with |- ex _ => eexists end)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - RRg; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - Hp4 Hqr2; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (spine; first [ eassumption | (intros E0; exfalso; first [ clear - E0 RRg; lia | lx_side_lia ]) | (intros E0; exfalso; first [ clear - E0; lia | lx_side_lia ]) | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "ERR4-EXQ3-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xaadb8 path 2: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xaadb8 path 2: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: match goal with E_ : ?lxq = ?lxq |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ ?lxq (seg_rom _)] => idtac | |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (subst rg) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (destruct (HLg eq_refl) as [Hq2 HqL2]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HLg; try clear Kz; try clear RRg| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "SERIAL") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ h3 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h3 _ _ mx HHx) as AB3 end end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "SER-1") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "SER-2") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "SER-3") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "SER-4") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "SER-5") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (destruct (x509_mismatch_select (q2 + bv_unsigned Lw) END 18446744073709542042 ltac:(first [ clear - Hp4 Hqr2 LR B1 B5; lia | lx_side_lia ]) ltac:(first [ clear - Hp4 B1 B5; lia | lx_side_lia ]) ltac:(clear; lia)) as (r' & ER & R1 & R2)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (change 18446744073709551615 with (Z.ones 64)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (rewrite Z.land_ones by (clear; lia)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (change (2 ^ 64) with 18446744073709551616) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (rewrite ER) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear ER| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with H : rw_cells _ ?mxc (AK + 24) _ |- _ => change (rw_cells asegs mxc (AK + 24) (seq_cells hct hcpad hcl hcp hcn)) in H end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold EXQ3) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (exists r', (q2 + bv_unsigned Lw)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat (lazymatch goal with |- ex _ => eexists end)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [destruct (Z.eq_dec (q2 + bv_unsigned Lw) END) as [E|NE]; [apply R1 in E; first [ clear - E; lia | lx_side_lia ]| specialize (R2 NE); first [ clear - R2; lia | lx_side_lia ]]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - Hp4 Hqr2 HqL2 LR; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (spine; first [ eassumption | (intros E0; destruct (Z.eq_dec (q2 + bv_unsigned Lw) END) as [EE|NE]; [exact EE| exfalso; specialize (R2 NE); first [ clear - R2 E0; lia | lx_side_lia ]]) | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SER-EXQ3-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xaadb8 path 3: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xaadb8 path 3: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xab82c) _ _ _ (seg_rom _)] => lx_apply mid_walk2 | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xab6e4) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- True => exact I | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lxw post_walk: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
